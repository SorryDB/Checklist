# SorryDB Agent development checklist

This is an artificial lean 4 project containing a number of sorried statements.
It intends to help with the development of SorryDB agents. 

The sorries in this project are *easy* from the point of view of automated
theorem proving, but represent individual engineering issues that may occur when
attempting to automatically fill sorries 'in the wild'.

## Contributing

Contributions are welcome. If you encounter (recurring) engineering issues that
may occur in automatically tring to fill sorries, feel free to make a PR.

Requirements:

1. Only `Prop`-valued sorries without metavariables (holes)
2. Please submit minimal working examples, so that each sorry representes a
   unique difficulty
3. Please include a proof string in the comments (replacing "sorry" with this
   string should close the sorry)

## TODO:

1. remove the proof strings, think of a "safe" place to store these. Document
   the sorries, with some guidance as to how to overcome the difficulties
2. use the SorryDB indexer to make a list of SorryDB indices for this project
   (even better: regularly update)


## Types of sorries



