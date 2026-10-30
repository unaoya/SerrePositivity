module

public import SerrePositivity.Asymptotic.RankQuotient
public import Mathlib.CategoryTheory.Localization.Linear
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift

/-!
# 自由列とランク商のスカラー作用

各段の線形写像へのスカラー作用を自由列の圏に入れる。
複体・ホモトピー圏・共通有界部分圏・ランク商の作用は既存の線形圏の構成で得る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 射のスカラー倍は段ごとの線形写像のスカラー倍である。 -/
instance : Linear R (FreeSequence R s) where
  homModule X Y := inferInstanceAs
    (Module R (∀ n, (Fin (X.rank n) → R) →ₗ[R] (Fin (Y.rank n) → R)))
  smul_comp _ _ _ a f g := by
    funext n
    exact LinearMap.comp_smul _ _ _
  comp_smul _ _ _ f a g := by
    funext n
    rfl

instance (n : ℕ) : (evaluation (R := R) (s := s) n).Linear R where
  map_smul := by intros; rfl

end SerrePositivity.Asymptotic.FreeSequence
