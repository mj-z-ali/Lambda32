import re
def coq_to_tex(coq_str: str) -> str:

    # Define patterns to replace and their replacements
    replacements = {
        "/\\": "\\land",
        "\\/": "\\lor",
        "¬": "\lnot "
    }

    # Iterate over the patterns and replace them
    for pattern, replacement in replacements.items():
        coq_str = coq_str.replace(pattern, replacement)

    # This function will be applied to every match of the pattern
    def subscript_replacer(match):
        return f"{match.group(1)}_{match.group(2)}"

    # Handle the 'a0' to 'a_0' style replacements
    return re.sub(r"([a-zA-Z])(\d+)", subscript_replacer, coq_str)

