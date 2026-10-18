module

public import SerrePositivity.KST.ProExcision.SplitConnecting
public import SerrePositivity.KST.ProExcision.KoszulFirstPage

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 合成射の cone の連結写像

概要：スペクトル対象の区間間の連結写像を、実際の商の短完全列の連結写像へ移す。
方針：cone 合成三角形の第三射を、右の cone の境界と左の cone への包含に分解する。
規約：cone から商への標準比較射を明示する。
使われ方：KST Lemma 4.10 の初頁微分と分裂境界の接続。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type u} [CommRing R]

/-- 概要：cone 三角形の連結写像を短完全列の連結写像で計算する。
方針：Mathlib のホモトピー圏での比較からホモロジー比較同型を相殺する。
規約：実際の cone から商への標準射を使用する。
使われ方：KST Lemma 4.10 のスペクトル対象の δ の具体化。 -/
theorem coneConnecting_eq_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
      (CochainComplex.mappingCone.triangle S.f).mor₃ i (i + 1) (by omega) =
      homologyMap (CochainComplex.mappingCone.descShortComplex S) i ≫ hS.δ i (i + 1) rfl := by
  have h := CochainComplex.mappingCone.homologySequenceδ_triangleh hS i (i + 1) rfl
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at h
  apply (cancel_mono
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.up ℤ) (i + 1)).inv.app S.X₁)).mp
  apply (cancel_epi
    ((HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.up ℤ) i).hom.app
      (CochainComplex.mappingCone S.f))).mp
  exact h

/-- 概要：cone の合成三角形の連結写像を、右の短完全列の δ と左の商への射で計算する。
方針：第三射の分解と cone から商への比較の包含との可換性を使う。
規約：二つの短完全列は同じ中間複体を共有する。
使われ方：KST Lemma 4.10 の隣接濾過区間の比較。 -/
theorem coneCompositeConnecting_quotient
    {X₀ X₁ X₂ Q₀ Q₁ : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (p : X₁ ⟶ Q₀) (q : X₂ ⟶ Q₁)
    (hf : f ≫ p = 0) (hg : g ≫ q = 0)
    (hT : (ShortComplex.mk g q hg).ShortExact) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
      (CochainComplex.mappingConeCompTriangle f g).mor₃ i (i + 1) (by omega) ≫
        homologyMap (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk f p hf))
          (i + 1) =
      homologyMap (CochainComplex.mappingCone.descShortComplex (ShortComplex.mk g q hg)) i ≫
        hT.δ i (i + 1) rfl ≫ homologyMap p (i + 1) := by
  rw [CochainComplex.mappingConeCompTriangle_mor₃, Functor.shiftMap_comp]
  rw [coneConnecting_eq_shortExact (ShortComplex.mk g q hg) hT i]
  simp only [CochainComplex.homologyFunctor_shift, Category.assoc]
  erw [← homologyMap_comp, CochainComplex.mappingCone.inr_descShortComplex]

end SerrePositivity.KST.ProExcision
