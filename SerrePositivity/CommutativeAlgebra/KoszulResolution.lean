module

public import SerrePositivity.CommutativeAlgebra.KoszulExact
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Koszul 複体を射影分解に仕立てる

`x` の Koszul 複体が `R/(x)` の分解（`IsKoszulResolution`）なら、`IsResolutionOf` の条件を
みたすので（各項は有限自由加群の直和で射影的）、`toChain (koszulComplex x)` は
`ModuleCat.of R (R ⧸ (x))` の `ProjectiveResolution` になる。

添加写像 `koszulAugmentation : K(x) → (R/(x))[0]` は擬同型（`K(x)` を `R/(x)` の K 射影分解として
使うときの形。`PerfectComplex/KoszulGeneration.lean`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 添加写像 -/

section augmentation

variable {n : ℕ} {x : Fin n → R}

lemma koszulComplex_d_zero_one : (koszulComplex x).d 0 1 = 0 :=
  (koszulComplex_isZero_X_of_pos x 1 one_pos).eq_of_tgt _ _

variable (hx : IsKoszulResolution x)

/-- `H^0(K(x)) ≅ R/(x)`。 -/
noncomputable def koszulH0Iso :
    (koszulComplex x).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.span (Set.range x)) :=
  hx.equiv.some.toModuleIso

/-- 添加写像 `K(x) → (R/(x))[0]`。 -/
noncomputable def koszulAugmentation :
    koszulComplex x ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) :=
  toSingleOfHomology (koszulComplex x) koszulComplex_d_zero_one (koszulH0Iso hx).hom

instance quasiIso_koszulAugmentation : QuasiIso (koszulAugmentation hx) :=
  quasiIso_toSingleOfHomology _ _ _ hx.isZero

end augmentation

/-! ## 射影分解 -/

variable {n : ℕ} (x : Fin n → R) (hx : IsKoszulResolution x)

/-- `K(x)` は `R/(x)` の分解（`IsResolutionOf` の形）。 -/
noncomputable def isResolutionOf_koszul :
    IsResolutionOf (koszulComplex x) (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) where
  isZero_X := koszulComplex_isZero_X_of_pos x
  projective := koszulComplex_projective_X x
  isZero_homology := hx.isZero
  homologyZeroIso := hx.equiv.some.toModuleIso

/-- **Koszul 分解**：`x` が `R/(x)` の Koszul 分解を与えるなら、`toChain K(x)` は
`ModuleCat.of R (R ⧸ (x))` の射影分解。 -/
noncomputable def koszulResolution :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) :=
  (isResolutionOf_koszul x hx).toProjectiveResolution

end SerrePositivity
