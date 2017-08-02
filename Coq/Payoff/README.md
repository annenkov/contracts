# Certified compilation of financial contracts

- [ILSyntax.v](ILSyntax.v) defines syntax of the payoff expressions language (PEL)
- [ILSemantics.v](ILSemantics.v) semantics of the PEL
- [ILTranslation.v](ILTranslation.v) defines compilation from the financial contracts DSL to PEL. Includes proof of compilation soundness
- [CutPayoff.v](CutPayoff.v) defines the cutPayoff transformation, which allows to parametarize the compiled code  with "current time" parameter. Manipulation this parameter one recover evolution of the contract over time in the form of payoff expression. Also contains proofs of soundness wrt. contract reduction semantics.
- [CutPayoffN.v](CutPayoffN.v) an (unfinished) generalization of theorems about cutPayoff to n-step reduction case.
- [Days.v](Days.v) defines functions allowing to extract information about transaction dates and dates of observable values (like stocks prices),which contract depends on. Could be used for reindexing transformation for array representation of the  external environment.
