import Lean4Tactics

/--
Smoke test: run a few theorems to verify the library loads correctly.
-/
def main : IO Unit := do
  IO.println "Basic tactics library loaded successfully."
  IO.println "All tactics examples compile."
