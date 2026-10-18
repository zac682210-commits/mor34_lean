# Compiler notes for the construction checkpoint

The accepted source is bdfd84d19dc1f9b36ecf9d8f595137854af8b47d.
The successful run is 39125116229, job 117668493060. The artifact digest and source
blob comparison are in construction_verified_metadata.json and
source_hashes_construction_20261018.json. These identify the tested source before
the documentation-only commit. Earlier failed attempts remain in branch history;
they are not counted as accepted proofs.

Resolved integration issues:

- List.length_finRange has an implicit length parameter in this Mathlib version;
  passing an extra argument is a type error.
- chargedClassAdjacencies needs its dependent class-size function m supplied
  explicitly in theorem headers and some theorem applications.
- A projected pair behind a let-bound construction needs dsimp, rather than only
  unfold, before omega can see the numeric cost field.
- Replacing a supplied stored table by its definition must rewrite both the
  bound hypothesis and the conclusion; equality does not itself align the two
  cost expressions inside arithmetic automation.
- An Option.get equality with proof-dependent arguments was handled by a local
  equality lemma at the concrete normal-table type. A polymorphic local Type*
  lemma introduced an unwanted universe parameter during elaboration.
- A conditional row constructor required rewriting builtPrefixRow_value after
  splitting its condition, because the projected conditional had blocked the
  earlier simplification.

No goal was weakened to fix these errors. No `sorry`, project axiom, unchecked
native decision, or new trusted external result was used. All new theorem names
are included in both Check.lean and the fail-closed transitive axiom allowlist.

The artifact contains ten log/result files. All nine recorded commands exit 0.
The dependency manifest equals the local pinned manifest; all 173 source/config
blobs match the accepted Git tree. Model, Targets and PaperInterface retain the
previous frozen hashes. Same-session evidence verification is not an independent
kernel replay.
