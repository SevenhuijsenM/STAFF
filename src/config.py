"""
Configuration management for formalspecc pipeline.

API keys can be set via:
1. Environment variables (recommended)
2. config.json file (gitignored)
3. Direct configuration in code

Usage:
    from config import Config
    
    config = Config()
    client = OpenAI(api_key=config.openai_api_key)
"""

import os
import json
from pathlib import Path
from typing import Optional


class Config:
    DEFAULT_CONFIG_FILE = "config.json"
    
    def __init__(self, config_file: Optional[str] = None):
        self.config_file = config_file or self.DEFAULT_CONFIG_FILE
        self._config = self._load_config()
    
    def _load_config(self) -> dict:
        config = {}
        
        if os.path.exists(self.config_file):
            with open(self.config_file, 'r') as f:
                config = json.load(f)
        
        return config
    
    def _save_config(self):
        with open(self.config_file, 'w') as f:
            json.dump(self._config, f, indent=4)
    
    @property
    def openai_api_key(self) -> str:
        return os.environ.get("OPENAI_API_KEY") or self._config.get("openai_api_key", "")
    
    @openai_api_key.setter
    def openai_api_key(self, value: str):
        self._config["openai_api_key"] = value
        self._save_config()
    
    @property
    def anthropic_api_key(self) -> str:
        return os.environ.get("ANTHROPIC_API_KEY") or self._config.get("anthropic_api_key", "")
    
    @anthropic_api_key.setter
    def anthropic_api_key(self, value: str):
        self._config["anthropic_api_key"] = value
        self._save_config()
    
    @property
    def default_model(self) -> str:
        return self._config.get("default_model", "gpt-5.2")
    
    @default_model.setter
    def default_model(self, value: str):
        self._config["default_model"] = value
        self._save_config()
    
    @property
    def input_dir(self) -> str:
        return self._config.get("input_dir", "input")
    
    @input_dir.setter
    def input_dir(self, value: str):
        self._config["input_dir"] = value
        self._save_config()
    
    @property
    def output_dir(self) -> str:
        return self._config.get("output_dir", "output")
    
    @output_dir.setter
    def output_dir(self, value: str):
        self._config["output_dir"] = value
        self._save_config()
    
    def get(self, key: str, default=None):
        return self._config.get(key, default)
    
    def set(self, key: str, value):
        self._config[key] = value
        self._save_config()
    
    @classmethod
    def setup(cls, openai_key: str = None, model: str = "gpt-5.2"):
        config = cls()
        if openai_key:
            config.openai_api_key = openai_key
        config.default_model = model
        return config
    
    def validate(self) -> tuple[bool, str]:
        if not self.openai_api_key:
            return False, "OpenAI API key not set. Set via OPENAI_API_KEY env var or config.json"
        return True, "Configuration valid"


def create_sample_config():
    sample = {
        "openai_api_key": "your-api-key-here",
        "anthropic_api_key": "",
        "default_model": "gpt-5.2",
        "input_dir": "input",
        "output_dir": "output"
    }
    return sample
