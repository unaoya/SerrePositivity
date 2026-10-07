module

public import SerrePositivity.KoszulExact
public import SerrePositivity.ResolutionOfCochain
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Koszul 複体を射影分解に仕立てる

`x` の Koszul 複体が `R/(x)` の分解（`IsKoszulResolution`）なら、`IsResolutionOf` の条件を
みたすので（各項は有限自由加群の直和で射影的）、`toChain (koszulComplex x)` は
`ModuleCat.of R (R ⧸ (x))` の `ProjectiveResolution` になる。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- Koszul 複体の各項は射影的（有限自由加群の直和）。 -/
lemma koszulComplex_projective_X :
    ∀ {n : ℕ} (x : Fin n → R) (i : ℤ), Projective ((koszulComplex x).X i)
  | 0, x, i => by
    rw [koszulComplex_zero]
    by_cases hi : i = 0
    · subst hi
      exact Projective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).projective
  | n + 1, x, i => by
    rw [koszulComplex_succ]
    have := koszulComplex_projective_X (Fin.init x) (i + 1)
    have := koszulComplex_projective_X (Fin.init x) i
    exact Projective.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (smulId (x (Fin.last n)) (koszulComplex (Fin.init x))) i (i + 1) rfl).symm inferInstance

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
