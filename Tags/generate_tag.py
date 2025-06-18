#!/usr/bin/env python3

import random
import string

def generate_tag():
    """Generate a random 2-character alphanumeric tag, avoiding O/0 and 1/I,
    with first character guaranteed to be a letter."""
    # Define allowed characters: letters and digits minus confusing ones
    letters = string.ascii_uppercase.replace('O', '').replace('I', '')  # Remove O and I
    digits = string.digits.replace('0', '').replace('1', '')  # Remove 0 and 1
    
    # Create the tag with guaranteed letter
    tag = ""
    tag += random.choice(letters)  
    tag += random.choice(letters + digits)  
    
    return tag

if __name__ == "__main__":
    # Generate and print a random tag
    tag = generate_tag()
    print(tag) 