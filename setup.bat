@echo off
REM Setup virtual environment for formalspecc (Windows)

echo Setting up formalspecc virtual environment...

set VENV_DIR=venv

REM Create virtual environment if it doesn't exist
if not exist %VENV_DIR% (
    echo Creating virtual environment...
    python -m venv %VENV_DIR%
)

REM Activate virtual environment
call %VENV_DIR%\Scripts\activate.bat

REM Upgrade pip
echo Upgrading pip...
python -m pip install --upgrade pip

REM Install dependencies
echo Installing dependencies...
pip install -r requirements.txt

echo.
echo Virtual environment setup complete!
echo To activate the environment, run:
echo   %VENV_DIR%\Scripts\activate.bat
echo.
echo To run the pipeline:
echo   python main.py --openai-key YOUR_KEY
