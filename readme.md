
Agda sources
---

This repository includes a lot of things that have not made it to my
thesis. The final library that is presented in my thesis is in the
[src/Cx](src/Cx) folder, and [src/Common.agda](src/Common.agda) is
used as well. The folder [src/Thesis](src/Thesis) contains code in the
thesis that is not directly taken from the actual library. Per
section, we indicate where the corresponding Agda code can be found:

- 1 Introduction ([Thesis/Introduction.agda](src/Thesis/Introduction.agda))
- 2 Usage ([Thesis/Usage.agda](src/Thesis/Usage.agda))
- 3 Generics and ornaments ([Thesis/Sop.agda](src/Thesis/Sop.agda))
  - 3.1 Descriptions
  - 3.2 Maps and folds
  - 3.3 Ornaments
  - 3.4 Ornamental algebras
  - 3.5 Discussion
    - 3.5.1 Σ-descriptions ([Thesis/SigmaDesc.agda](src/Thesis/SigmaDesc.agda))
    - 3.5.2 Finding the right ornaments
- 4 Ornaments on dependently typed descriptions ([Thesis/Simple.agda](src/Thesis/Simple.agda))
  - 4.1 Contexts and environments ([Thesis/SimplifiedContexts.agda](src/Thesis/SimplifiedContexts.agda))
  - 4.2 Descriptions ([Cx/Simple/Desc.agda](src/Cx/Simple/Desc.agda))
  - 4.3 Ornaments ([Cx/Simple/Ornament.agda](src/Cx/Simple/Ornament.agda))
- 5 Ornaments on families of datatypes ([Thesis/Extended.agda](src/Thesis/Extended.agda))
  - 5.1 Descriptions ([Cx/Extended/Desc.agda](src/Cx/Extended/Desc.agda))
  - 5.2 Ornaments ([Cx/Extended/Ornament.agda](src/Cx/Extended/Ornament.agda))
  - 5.3 Algebraic ornaments ([Cx/Extended/AlgebraicOrnament.agda](src/Cx/Extended/AlgebraicOrnament.agda))
  - 5.4 Discussion
    - 5.4.1 Separating parameters from contexts ([Thesis/SeparateContexts.agda](src/Thesis/SeparateContexts.agda))
- 6 Generic programming with descriptions ([Thesis/Named.agda](src/Thesis/Named.agda))
  - 6.1 Descriptions and ornaments ([Cx/Named/Desc.agda](src/Cx/Named/Desc.agda), [Cx/Named/Ornament.agda](src/Cx/Named/Ornament.agda), [Cx/Named/AlgebraicOrnament.agda](src/Cx/Named/AlgebraicOrnament.agda))
  - 6.2 Quoting datatypes ([Cx/Quoting.agda](src/Cx/Quoting.agda))
  - 6.3 Deriving an embedding-projection pair ([Cx/HasDesc/Derive.agda](src/Cx/HasDesc/Derive.agda))
  - 6.4 Generic functions ([Cx/GenericOperations.agda](src/Cx/GenericOperations.agda))
  - 6.5 Unquoting descriptions ([Cx/Unquoting.agda](src/Cx/Unquoting.agda))
  - 6.6 Higher-level ornaments ([Cx/Named/MoreOrnaments.agda](src/Cx/Named/MoreOrnaments.agda))
    - 6.6.1 Structure-preserving ornaments
    - 6.6.2 Ornament composition
    - 6.6.3 More ornaments
    - 6.6.4 Reornaments ([Cx/Named/AlgebraicOrnaments.agda](src/Cx/Named/AlgebraicOrnaments.agda))
  - 6.7 Discussion
    - 6.7.1 Embedding-projection instances
- 7 Discussion ([Thesis/Discussion.agda](src/Thesis/Discussion.agda))
  - 7.1 Explicit parameter use ([Thesis/DiscussionTermLang.agda](src/Thesis/DiscussionTermLang.agda))
  - 7.2 Induction-recursion and strict positivity
- 8 Conclusion
  - 8.1 Future work
