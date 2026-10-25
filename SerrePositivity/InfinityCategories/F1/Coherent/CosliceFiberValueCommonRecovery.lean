module

public import SerrePositivity.InfinityCategories.F1.Coherent.TwoSidedHomLeftEndpoint
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEquivalence

/-!
概要：共通 Hom 解像上で、左 coslice 比較と既存の右 Hom 値回収を照合する。
方針：固定端点の左右 Hom ホモトピーに、既存の区間比較と coherent Hom の逆を合成する。
規約：値回収で選ばれた逆をそのまま使い、独立の fiber 同値を選び直さない。
使われ方：Ind-S (5) の指定 unstraightening の全 fiber 単位の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 左 coslice の元の比較を、指定右 Hom 回収へ送ると同じ共通解像の右射影になる。 -/
def coherentCosliceFiberValueCommonIso {C : Type v} [Category.{u} C]
    [SimplicialCategory C] [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    (X Y : C) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        HomotopyLimits.coherentCosliceFiberComparison X Y ≫
        (cosliceFiberPinchedLeftIso (coherentNerveVertex X) (coherentNerveVertex Y)).hom ≫
        (pinchedHomLeftRightEquivalence (coherentNerveVertex X) (coherentNerveVertex Y)).hom ≫
        (coherentHomEquivalence X Y).inv)
      ((SSet.uliftFunctor.{v, u}).map (edgewiseRight (SimplicialCategory.sHom X Y))) := by
  let r := (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (coherentNerveVertex X) (coherentNerveVertex Y)).choose
  let h := coherentHomEquivalence X Y
  let a := (SSet.uliftFunctor.{v, u}).map (edgewiseRight (SimplicialCategory.sHom X Y))
  have e₀ := functorIsoOfSimplicialHomotopy (coherentTwoSidedHomIntervalHomotopy X Y)
  have e₁ := FunctorIso.postcomp e₀ (r.inv ≫ h.inv)
  have e₂ := FunctorIso.postcomp (FunctorIso.precomp r.homInvIso (a ≫ h.hom)) h.inv
  have e₃ := FunctorIso.precomp h.homInvIso a
  simp only [Category.assoc, Category.comp_id] at e₂ e₃
  have e := e₁ ≪≫ e₂ ≪≫ e₃
  change FunctorIso
    ((SSet.uliftFunctor.{v, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
      HomotopyLimits.coherentCosliceFiberComparison X Y ≫
      (cosliceFiberPinchedLeftIso (coherentNerveVertex X) (coherentNerveVertex Y)).hom ≫
      ((cosliceFiberPinchedLeftIso (coherentNerveVertex X) (coherentNerveVertex Y)).inv ≫
        cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)) ≫
      r.inv ≫ h.inv) a
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using e

end SerrePositivity.InfinityCategories
