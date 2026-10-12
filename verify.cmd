@echo off
setlocal
chcp 65001 >nul
where pwsh >nul 2>nul
if errorlevel 1 (
  powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0Verify.ps1" %*
) else (
  pwsh -NoProfile -ExecutionPolicy Bypass -File "%~dp0Verify.ps1" %*
)
set "result=%errorlevel%"
if /i not "%CI%"=="true" pause
exit /b %result%
