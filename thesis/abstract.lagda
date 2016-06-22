%include thesis.fmt

\begin{abstract}
  Modern dependently typed functional programming languages like Agda
  allow very specific restrictions to be built into datatypes by using
  indices and dependent types. Properly restricted types can help
  programmers to write correct-by-construction software. However, code
  duplication will occur because the language does not recognise that
  similarly-structured datatypes with slightly different
  program-specific restrictions can be related. Some functions will be
  copy-pasted for lists, vecs, sorted lists and bounded lists.

  Ornaments specify the exact relatedness of different datatypes and
  may be a path towards a solution. It is a first step in structuring
  the design space of datatypes in dependently typed
  languages. Literature has shown how ornaments can produce conversion
  functions between types, and how they can help to recover code reuse
  by transporting functions across ornaments.

  This thesis presents an Agda library for experimentation with
  ornaments. We have implemented a generic programming framework where
  datatypes are represented as descriptions. A description can be
  generated from a real datatype and patched with an ornament to
  create new description, which in turn can be converted back to a new
  datatype.

  Our descriptions are unconvential, because they are carefully
  designed to always be convertible to actual datatypes. They pass
  along a context internally to support dependent types and they can
  be used with multiple parameters and multiple indices.
\end{abstract}
