
module Cx.Named.Mutations where

open import Common
open import Cx.Named.AlgebraicOrnament

idOrn : ∀{I Γ Δ dt c}{D : Desc I Γ dt} → DefOrn I id Δ c D
idOrn {dt = isCon} {c} {ι o} = ι (λ δ → inv (o (c δ)))
idOrn {dt = isCon} {c} {nm / S ⊗ xs} = nm /-⊗ idOrn
idOrn {dt = isCon} {c} {nm /rec i ⊗ xs} = nm /rec (λ δ → inv (i (c δ))) ⊗ idOrn
idOrn {dt = isDat _} {c} {`0} = `0
idOrn {dt = isDat _} {c} {x ⊕ xs} = idOrn ⊕ idOrn

idOrn-identity : ∀{I Γ dt}{D : Desc I Γ dt} → ornToDesc (idOrn {c = id} {D = D}) ≡ D
idOrn-identity {dt = isCon} {ι o} = refl
idOrn-identity {dt = isCon} {nm / S ⊗ xs} = cong (_/_⊗_ nm S) idOrn-identity
idOrn-identity {dt = isCon} {nm /rec i ⊗ xs} = cong (_/rec_⊗_ nm i) idOrn-identity
idOrn-identity {dt = isDat .0}{ `0} = refl
idOrn-identity {dt = isDat _} {x ⊕ xs} = cong₂ _⊕_ idOrn-identity idOrn-identity

updateConstructor : ∀{I Γ #c}{D : DatDesc I Γ #c} → (k : Fin #c) →
                    ∀{Δ c} → DefOrn I id Δ c (lookupCtor D k) →
                    DefOrn I id Δ c D
updateConstructor {D = `0} () o
updateConstructor {D = x ⊕ xs} zero o = o ⊕ idOrn
updateConstructor {D = x ⊕ xs} (suc k) o = idOrn ⊕ updateConstructor k o

-- We are using the value of the parameter as the type of the argument, so we
-- can only use Set.
addParameterArg : ∀{I Γ #c}{D : DatDesc I Γ #c} → Fin #c → String →
                DefOrn I id (Γ ▷₁′ Set) pop D
addParameterArg k str = updateConstructor k (str / top +⊗ idOrn)

conRenameArguments : ∀{I Γ}{D : ConDesc I Γ} → Vec (Maybe String) (countArguments D) → Orn id id D
conRenameArguments {D = ι o} [] = ι (inv ∘ o)
conRenameArguments {D = nm / S ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /-⊗ (conRenameArguments nms)
conRenameArguments {D = nm /rec i ⊗ xs} (nm′ ∷ nms) = maybe nm id nm′ /rec (inv ∘ i) ⊗ conRenameArguments nms

renameArguments : ∀{I Γ #c}{D : DatDesc I Γ #c}(k : Fin #c) →
                  Vec (Maybe String) (countArguments (lookupCtor D k)) → Orn id id D
renameArguments k nms = updateConstructor k (conRenameArguments nms)
