syntax "lemma " declId declSig " := " term : command
macro_rules
  | `(lemma $id $sig := $proof) => `(theorem $id $sig := $proof)

syntax "corollary " optDeclSig " := " term : command
macro_rules
  | `(corollary $sig := $proof) => `(example $sig := $proof)
