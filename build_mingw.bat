@echo off
setlocal
where gcc >nul 2>nul
if errorlevel 1 (
  echo ERROR: gcc was not found. Add MinGW-w64 to PATH and try again.
  exit /b 1
)
gcc -std=c11 -O2 -Wall -Wextra -Wpedantic "%~dp0lloyd.c" -o "%~dp0lloyd.exe"
if errorlevel 1 exit /b %errorlevel%
echo Built %~dp0lloyd.exe
endlocal
