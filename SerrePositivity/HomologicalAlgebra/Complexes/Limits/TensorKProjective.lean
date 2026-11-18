module

public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# K-projective 複体のテンソル

概要：二つの K-projective 複体の実テンソルは K-projective。
方針：元の閉随伴で転置し、全 Hom の非輪状性と実テンソルのホモトピーを使う。
規約：任意可換環・非有界複体で成立する。
使われ方：cofibrant 始域と正規化単体のテンソル模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma tensor_isKProjective (X Y : Complex A) [X.IsKProjective] [Y.IsKProjective] :
    CochainComplex.IsKProjective (X ⊗ Y) where
  nonempty_homotopy_zero {L} f hL := by
    let t := tensorHomEquiv X Y L f
    let h := IsKProjective.homotopyZero t (homComplex_acyclic_of_isKProjective A X L hL)
    have hh := mapBifunctorMapHomotopy₂ (𝟙 X) h (curriedTensor (ModuleCat A)) (.up ℤ)
    change Homotopy (𝟙 X ⊗ₘ t) (𝟙 X ⊗ₘ 0) at hh
    have he : (𝟙 X ⊗ₘ t) ≫ (ihom.ev X).app L = f := by
      change (tensorLeft X).map t ≫ (ihom.adjunction X).counit.app L = f
      exact ((ihom.adjunction X).homEquiv_counit (g := t)).symm.trans
        ((tensorHomEquiv X Y L).symm_apply_apply f)
    have ht := hh.compRight ((ihom.ev X).app L)
    rw [he] at ht
    exact ⟨by simpa using ht⟩

end SerrePositivity.ComplexLimits
