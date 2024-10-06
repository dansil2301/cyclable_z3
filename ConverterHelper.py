import z3

from typing import Any


class ConverterHelper:
    @staticmethod
    def convert_to_type(var_type: Any, var_value: str) -> Any:
        if type(var_type) is z3.Int:
            return int(var_value)
        elif type(var_type) is z3.Bool:
            return bool(var_value)
        elif type(var_type) is z3.Real:
            return float(var_value)
