import «Naturals»

def main : IO Unit :=
  do IO.println (String.append (String.append
    "Where's the code execution?"
    "Turns out, proving the natural numbers is done at compile time.")
    "Thus successful compilation implies proof correctness!")
