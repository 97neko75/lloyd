@echo off
setlocal
where cl >nul 2>nul
if errorlevel 1 (
  echo ERROR: cl.exe was not found. Run this script from a Visual Studio Developer Command Prompt.
  exit /b 1
)
cl /nologo /std:c11 /W4 /D_CRT_SECURE_NO_WARNINGS "%~dp0lloyd.c" /Fe:"%~dp0lloyd.exe"
if errorlevel 1 exit /b %errorlevel%
echo Built %~dp0lloyd.exe
endlocal
