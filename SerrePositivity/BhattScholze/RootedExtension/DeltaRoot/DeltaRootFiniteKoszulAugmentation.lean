module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootFiniteKoszulCoefficients
public import SerrePositivity.HomologicalAlgebra.KoszulModuleBounds
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift

/-! # 根関係の係数付きKoszul複体から実商への擬同型

既存反復錐複体と実際の(Q⊗_A N)[0]の間の写像を供給する。
係数側(p,d)の正則性・係数加群の平坦性は不要。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (b : σ → A) {n : ℕ} (s : Fin n → σ) (hs : Function.Injective s)
variable (N : Type u) [AddCommGroup N] [Module A N]

include hs in
/-- 根関係の係数付きKoszul複体は、すべての非零次数でホモロジーが零。 -/
theorem deltaRootFiniteKoszulCoefficientHomology_isZero_of_ne (k : ℤ) (hk : k ≠ 0) :
    IsZero (((koszulModuleFunctor
      (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).homology k) := by
  cases k with
  | ofNat i =>
      have hn : i ≠ 0 := by
        intro h
        subst i
        exact hk rfl
      have hi : 0 < (i : ℤ) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)
      exact isZero_homology_of_isZero_X _ _
        (koszulModuleFunctor_isZero_X_of_pos
          (fun j ↦ deltaRootRelationFamily (p := p) b (s j))
          (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N)) (i : ℤ) hi)
  | negSucc i =>
      simpa only [Int.natCast_add, Int.natCast_one, Int.negSucc_eq] using
        deltaRootFiniteKoszulCoefficientHomology_isZero (p := p) b s hs N i

omit [Fact p.Prime] in
/-- 根関係の係数付きKoszul複体の零次数から一次数への微分は零。 -/
theorem deltaRootFiniteKoszulCoefficient_d_zero :
    ((koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N))).d 0 1 = 0 :=
  (koszulModuleFunctor_isZero_X_of_pos _ _ 1 (by decide)).eq_of_tgt _ _

/-- 係数付き根関係Koszul複体から実通常テンソル積の単一複体への具体的写像。 -/
def deltaRootFiniteKoszulCoefficientAugmentation :
    (koszulModuleFunctor (fun j ↦ deltaRootRelationFamily (p := p) b (s j))).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A) N)) ⟶
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
        Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N)) :=
  toSingleOfHomology _ (deltaRootFiniteKoszulCoefficient_d_zero b s N)
    (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom

/-- 具体的な係数付き根関係添加写像は擬同型。 -/
theorem deltaRootFiniteKoszulCoefficientAugmentation_quasiIso :
    QuasiIso (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N) :=
  quasiIso_toSingleOfHomology _ (deltaRootFiniteKoszulCoefficient_d_zero b s N)
    (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom
    (deltaRootFiniteKoszulCoefficientHomology_isZero_of_ne b s hs N)

/-- 添加写像の零次ホモロジー射は、既存Tor比較から得た具体的な零次同型。 -/
theorem deltaRootFiniteKoszulCoefficientAugmentation_homologyMap :
    HomologicalComplex.homologyMap
      (deltaRootFiniteKoszulCoefficientAugmentation (p := p) b s hs N) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        (ModuleCat.of (MvPolynomial σ A) (TensorProduct A (MvPolynomial σ A ⧸
          Ideal.span (Set.range fun j ↦ deltaRootRelationFamily (p := p) b (s j))) N))).hom =
      (deltaRootFiniteKoszulCoefficientHomologyZeroEquiv b s hs N).toModuleIso.hom :=
  toSingleOfHomology_homologyMap _ (deltaRootFiniteKoszulCoefficient_d_zero b s N) _

end SerrePositivity.BhattScholze
