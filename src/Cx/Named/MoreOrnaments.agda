
module Cx.Named.MoreOrnaments where

open import Common
open import Cx.Named.AlgebraicOrnament

reCx : ∀{I J u Γ Δ c dt}{D : Desc I Γ dt} →
  (f : ∀ i → u ⁻¹ i) → Orn J u Δ c D
reCx {c = c} {isCon} {ι o} f = ι (f ∘ o ∘ c)
reCx {c = _} {isCon} {nm / S ⊗ xs} f = nm /-⊗ reCx f
reCx {c = c} {isCon} {nm /rec i ⊗ xs} f = nm /rec f ∘ i ∘ c ⊗ reCx f
reCx {c = _} {isDat _} {`0} f = `0
reCx {c = _} {isDat _} {x ⊕ xs} f = reCx f ⊕ reCx f

reindex : ∀{I J u Γ dt}{D : Desc I Γ dt} →
  (f : ∀ i → u ⁻¹ i) → Orn J u Γ id D
reindex = reCx

reparam : ∀{I Γ Δ c dt}{D : Desc I Γ dt} → Orn I id Δ c D
reparam = reCx inv

idOrn : ∀{I Γ dt}{D : Desc I Γ dt} → Orn I id Γ id D
idOrn = reCx inv

idOrn-identity : ∀{I Γ dt}{D : Desc I Γ dt} → ornToDesc (idOrn {D = D}) ≡ D
idOrn-identity {dt = isCon} {ι o} = refl
idOrn-identity {dt = isCon} {nm / S ⊗ xs} = cong (_/_⊗_ nm S) idOrn-identity
idOrn-identity {dt = isCon} {nm /rec i ⊗ xs} = cong (_/rec_⊗_ nm i) idOrn-identity
idOrn-identity {dt = isDat .0}{ `0} = refl
idOrn-identity {dt = isDat _} {x ⊕ xs} = cong₂ _⊕_ idOrn-identity idOrn-identity

updateConstructor : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  (k : Fin #c) → Orn I id Γ id (lookupCtor D k) →
  Orn I id Γ id D
updateConstructor {D = `0} () o
updateConstructor {D = x ⊕ xs} zero o = o ⊕ idOrn
updateConstructor {D = x ⊕ xs} (suc k) o =
  idOrn ⊕ updateConstructor k o

-- We are using the value of the parameter as the type of the argument, so we
-- can only use Set.
addParameterArg : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  Fin #c → String → Orn I id (Γ ▷₁′ Set) pop D
addParameterArg k str = reparam
  >>⁺ updateConstructor k (str / top +⊗ reparam)

conRenameArguments : ∀{I Γ}{D : ConDesc I Γ} →
  Vec (Maybe String) (countArguments D) →
  Orn I id Γ id D
conRenameArguments {D = ι o} [] = ι (inv ∘ o)
conRenameArguments {D = nm / S ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /-⊗ (conRenameArguments nms)
conRenameArguments {D = nm /rec i ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /rec (inv ∘ i) ⊗ conRenameArguments nms

renameArguments : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  (k : Fin #c) →
  Vec (Maybe String) (countArguments (lookupCtor D k)) →
  Orn I id Γ id D
renameArguments k nms = updateConstructor k (conRenameArguments nms)

conRenameArguments-none : ∀{I Γ}{D : ConDesc I Γ} →
  ornToDesc (conRenameArguments {D = D} (pure nothing)) ≡ D
conRenameArguments-none {D = ι o} = refl
conRenameArguments-none {D = nm / S ⊗ xs} = cong (_/_⊗_ nm S) conRenameArguments-none
conRenameArguments-none {D = nm /rec i ⊗ xs} = cong (_/rec_⊗_ nm i) conRenameArguments-none

renameArguments-none : ∀{I Γ #c}{D : DatDesc I Γ #c} →
  (k : Fin #c) → ornToDesc (renameArguments {D = D} k (pure nothing)) ≡ D
renameArguments-none {D = `0} ()
renameArguments-none {D = x ⊕ xs} zero = cong₂ _⊕_ conRenameArguments-none idOrn-identity
renameArguments-none {D = x ⊕ xs} (suc k) = cong₂ _⊕_ idOrn-identity (renameArguments-none k)
