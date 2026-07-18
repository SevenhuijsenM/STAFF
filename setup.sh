#!/bin/bash

# Setup virtual environment for formalspecc

set -e

VENV_DIR="venv"

echo "Setting up formalspecc virtual environment..."

# Create virtual environment if it doesn't exist
if [ ! -d "$VENV_DIR" ]; then
    echo "Creating virtual environment..."
    python3 -m venv "$VENV_DIR"
fi

# Upgrade pip
echo "Upgrading pip..."
"$VENV_DIR/bin/pip" install --upgrade pip

# Install dependencies
echo "Installing dependencies..."
"$VENV_DIR/bin/pip" install -r requirements.txt

echo ""
echo "Virtual environment setup complete!"
echo ""
echo "To activate the environment, run:"
echo "  source $VENV_DIR/bin/activate"
echo ""
echo "To run the pipeline:"
echo "  source venv/bin/activate && python main.py --openai-key YOUR_KEY"
