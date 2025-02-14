## TODO

# Misc

* eliminate odd crash of --prover spass examples/Maximum_principle.ftl:
  "Undefined symbol sdtcflbdtrb."

* more robust (less redundant) specification of options with their defaults:
  avoid duplicate information in Haskell sources, comments, init.opt


# PIDE markup reports

* def/ref markup fact names

* instructions: completion on errors -- more robust syntax for synonyms!?

* more robust parsing: recover from errors (e.g. via TextError construction)


# Admin

* systematic runs of "test" examples

* semi-automated distribution builds for Linux, macOS, Windows
  (e.g. appveyor, travis)


# General

* caching of old results from prefix of source, old versions etc.

* support for multiple (simultaneous) input files (!?)

* support for concatenated sources, according to Isabelle theory document (??)
  (e.g. multiple `forthel` commands, even forthel document-antiquotations)

* more robust and scalable library handling (imports) (!?)

* clarify treatment of non-ASCII text: Latex vs. Isabelle symbols (!?!)

* parallel checking: internal and/or external provers (??)

* formulate underlying logic + set-theory in Isabelle (syntax only, no rules):
  thus formulas can be pretty-printed via Isabelle notation


# Cosmetic

* Allow `\in`, `\mathrm{dom}`, and similar commands as primitives. The relevant code is in `SAD.ForTheL.Base.initFS`