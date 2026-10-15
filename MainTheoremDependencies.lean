import PerronWright
import Lean

/-! Reproducible inspection of checked Chapter 3 theorem expressions.

This file adds no mathematical assumption or proof. It reads the checked
environment, distinguishes type/proof constants, traverses their actual
constant dependencies, and separately invokes Lean's axiom collector.
Generated reports are local outputs, not imported by any proof module.
-/

open Lean Elab Command

namespace PerronWrightAudit

structure PaperMainTheorem where
  number : String
  title : String
  declarations : Array Name

/-- Paper numbering is not the number of separately checked Lean declarations.
The countable terminal jointly implements both 3.9 and 3.10. -/
def paperMainTheorems : Array PaperMainTheorem := #[
  { number := "3.6", title := "Perron--Wright formula", declarations := #[
  ``PerronWright.FiniteIrreduciblePerronWrightTerminal.finite_perronWright,
  ``PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem] },
  { number := "3.8", title := "Local factorial asymptotics and component process limit",
    declarations := #[
  ``PerronWright.FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density,
  ``PerronWright.CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus,
  ``PerronWright.ModelActualBrownianLimits.finite_windowLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.finite_processLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.finite_markedWindowLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.finite_markedProcessLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.finite_starredProcessLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.finite_starredMarkedProcessLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_windowLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_processLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_markedWindowLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_markedProcessLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_starredProcessLaw_tendsto_actual_Brownian,
  ``PerronWright.ModelActualBrownianLimits.compact_starredMarkedProcessLaw_tendsto_actual_Brownian] },
  { number := "3.9", title := "Countable type critical realization", declarations := #[
  ``PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits] },
  { number := "3.10", title := "Countable type limits without spectral renormalization",
    declarations := #[
  ``PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits] }
]

def supportingTheorems : Array Name := #[
  ``PerronWright.BrownianActualFactorialDensity.actual_ordered_source_factorial_density,
  ``PerronWright.BrownianActualFactorialDensity.actual_window_factorial_density,
  ``PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals,
  ``PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals
]

def mainDeclarations : Array Name := Id.run do
  let mut result := #[]
  for group in paperMainTheorems do
    for n in group.declarations do
      if !result.contains n then result := result.push n
  return result

def auditTargets : Array Name := mainDeclarations ++ supportingTheorems

def paperNumbers (n : Name) : Array String :=
  (paperMainTheorems.filter fun g => g.declarations.contains n).map (·.number)

def isProject (n : Name) : Bool :=
  n.toString.startsWith "PerronWright." || n.toString.startsWith "_private.PerronWright."

def sorted (xs : Array Name) : Array Name := xs.qsort Name.lt

def closure (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if !seen.contains n then
      seen := seen.insert n
      if let some ci := env.checked.get.find? n then
        todo := ci.getUsedConstantsAsSet.toArray.toList ++ todo
  return sorted seen.toArray

def kind (ci : ConstantInfo) : String := match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

structure DeclarationRecord where
  name : String
  kind : String
  module : String
  source : Option String
  line : Option Nat
  dependencies : Array String
  deriving ToJson

structure TheoremRecord where
  name : String
  role : String
  paperTheorems : Array String
  statement : String
  typeDependencies : Array String
  proofDependencies : Array String
  reachableConstants : Array String
  projectTheorems : Array String
  projectDefinitions : Array String
  axioms : Array String
  deriving ToJson

def declarationRecord (env : Environment) (n : Name) : CommandElabM DeclarationRecord := do
  let ci := env.checked.get.find? n
  let mod := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
  let ranges ← findDeclarationRanges? n
  return {
    name := n.toString
    kind := ci.map kind |>.getD "unknown"
    module := mod.map Name.toString |>.getD "builtin"
    source := mod.map fun m => String.intercalate "/" (m.toString.splitOn ".") ++ ".lean"
    -- Lean positions are 1-based; use the identifier selection, not its doc comment.
    line := ranges.map fun r => r.selectionRange.pos.line
    dependencies := ci.map (fun c => (sorted c.getUsedConstantsAsSet.toArray).map Name.toString)
      |>.getD #[]
  }

def theoremRecord (env : Environment) (n : Name) : CommandElabM TheoremRecord := do
  let some ci := env.checked.get.find? n | throwError "Missing audited declaration: {n}"
  unless kind ci == "theorem" do throwError "Not a theorem: {n}"
  let some proof := ci.value? (allowOpaque := true) |
    throwError "Proof expression unavailable: {n}; refusing a type-only dependency report"
  let ds := sorted ci.type.getUsedConstantsAsSet.toArray
  let ps := sorted proof.getUsedConstantsAsSet.toArray
  if ps.isEmpty then throwError "Empty proof dependencies for {n}"
  let reach := closure env (ds ++ ps)
  let axioms ← collectAxioms n
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Nonstandard axiom in {n}: {ax}"
  let statement ← liftTermElabM <| Meta.ppExpr ci.type
  return {
    name := n.toString
    role := if (paperNumbers n).isEmpty then "supporting result" else "main theorem implementation"
    paperTheorems := paperNumbers n
    statement := statement.pretty
    typeDependencies := ds.map Name.toString
    proofDependencies := ps.map Name.toString
    reachableConstants := reach.map Name.toString
    projectTheorems := (reach.filter fun d => isProject d &&
      ((env.checked.get.find? d).map kind == some "theorem")).map Name.toString
    projectDefinitions := (reach.filter fun d => isProject d &&
      ((env.checked.get.find? d).map kind != some "theorem")).map Name.toString
    axioms := axioms.map Name.toString
  }

run_cmd do
  let env := (← getEnv).setExporting false
  let mut results : Array TheoremRecord := #[]
  for n in auditTargets do
    let r ← theoremRecord env n
    results := results.push r
  let union := closure env auditTargets
  let declarations ← union.mapM (declarationRecord env)
  for d in declarations do
    if d.kind == "unknown" then
      throwError "Cannot inspect reachable declaration: {d.name}; refusing an incomplete report"
  let report := Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("leanVersion", toJson Lean.versionString),
    ("mainTheoremCount", toJson paperMainTheorems.size),
    ("implementationDeclarationCount", toJson mainDeclarations.size),
    ("supportingDeclarationCount", toJson supportingTheorems.size),
    ("auditedDeclarationCount", toJson results.size),
    ("paperMainTheorems", toJson (paperMainTheorems.map fun g => Json.mkObj [
      ("number", toJson g.number), ("title", toJson g.title),
      ("declarations", toJson (g.declarations.map Name.toString))])),
    ("supportingTheorems", toJson (supportingTheorems.map Name.toString)),
    ("theorems", toJson results),
    ("declarations", toJson declarations)
  ]
  liftIO <| IO.FS.createDirAll ".verification"
  liftIO <| IO.FS.writeFile ".verification/main-theorem-dependencies.json" report.compress
  -- Invoke Lean's own command; preserve each complete message without regrouping
  -- declarations, renaming them, or reconstructing the axiom list ourselves.
  let start := (← get).messages.toArray.size
  for n in mainDeclarations do
    elabCommand (← `(#print axioms $(mkIdent n)))
  let messages := (← get).messages.toArray
  let mut nativeOutput := ""
  for message in messages.extract start messages.size do
    nativeOutput := nativeOutput ++ (← message.data.toString) ++ "\n"
  liftIO <| IO.FS.writeFile ".verification/main-theorem-axioms.txt" nativeOutput
  let mut md := "# Definitions reachable from the four paper main theorems and their supporting results\n\n"
  md := md ++ "Generated from checked Lean expressions by `MainTheoremDependencies.lean`.\n"
  md := md ++ "Paper main theorems: 3.6, 3.8, 3.9 and 3.10; 17 distinct implementation declarations and four supporting declarations.\n"
  md := md ++ "This includes type and proof dependencies, generated helpers and private declarations.\n"
  md := md ++ "Mathlib/Lean declarations remain in the full JSON report, not in this project-only index.\n\n"
  md := md ++ "| Fully qualified declaration | Kind | Source |\n| --- | --- | --- |\n"
  for d in declarations do
    if (d.name.startsWith "PerronWright." || d.name.startsWith "_private.PerronWright.") &&
        d.kind != "theorem" then
      let location := match d.source with
        | some p =>
          let suffix := d.line.map (fun l => s!"#L{l}") |>.getD ""
          s!"[{p}{suffix}](../{p}{suffix})"
        | none => "generated / builtin"
      md := md ++ s!"| `{d.name}` | {d.kind} | {location} |\n"
  liftIO <| IO.FS.writeFile ".verification/main-theorem-definitions.md" md
  logInfo m!"DEPENDENCY AUDIT PASSED: {paperMainTheorems.size} paper main theorems; {results.size} audited Lean declarations ({mainDeclarations.size} implementation + {supportingTheorems.size} supporting); {declarations.size} reachable constants. Reports: .verification/"

end PerronWrightAudit
