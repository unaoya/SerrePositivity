module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentPointedRestriction
public import SerrePositivity.InfinityCategories.Core.UniverseLimits

/-!
概要：元の全錐の持ち上げの切断制限を、像の実際の native 全錐の制限へ照合する。
方針：元の join の宇宙同型を底上の同型にし、同じ右因子包含の前合成を共役する。
規約：全錐と元の底図式の脚を保持。頂点だけの比較ではない。
使われ方：元の Yoneda の像の native な錐における一点からの切断判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全錐の宇宙持ち上げと、元の錐の native な持ち上げは底上で同型。 -/
def liftedConeShapeOverIso {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map c.val) ≅
      Over.mk (JoinCone.ulift.{u, u + 1} c).val :=
  Over.isoMk (uliftConeShapeIso.{u, u + 1} K 0) (by
    change (uliftConeShapeIso K 0).hom ≫
      ((uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map c.val) = _
    rw [Iso.hom_inv_id_assoc]
    rfl)

/-- 元の持ち上げた右包含を形状同型で写すと native な右包含になる。 -/
lemma liftedConeShapeOverIso_restriction {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D) :
    uliftOverMorphism (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
      (joinInr (Δ[0] : SSet.{u}) K) c.property) ≫ (liftedConeShapeOverIso c).hom =
    Over.homMk (U := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map D))
      (V := Over.mk (JoinCone.ulift.{u, u + 1} c).val)
      (joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))
      (JoinCone.ulift.{u, u + 1} c).property := by
  apply Over.OverMorphism.ext
  exact uliftConeShapeIso_inr K 0

/-- 元の pointed 制限の同値性は、像の実際の native 全錐の同じ制限の同値性へ移る。 -/
lemma coherentPointedRestriction_nativeCone_isQCatEquivalence
    {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (h : IsQCatEquivalence (coherentPointedRestriction F
      (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
        (joinInr (Δ[0] : SSet.{u}) K) c.property))) :
    IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
      (mapJoinCone F (JoinCone.ulift.{u, u + 1} c))) := by
  let g := uliftOverMorphism (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property)
  let e := (Over.map F).mapIso (liftedConeShapeOverIso c)
  let ep : relativeFunctorSpace pointedSpaceProjection
        ((JoinCone.ulift.{u, u + 1} c).val ≫ F) ≅
      relativeFunctorSpace pointedSpaceProjection
        ((SSet.uliftFunctor.{u + 1, u}).map c.val ≫ F) :=
    (relativeFunctorOverFunctor pointedSpaceProjection).mapIso e.op
  have he : IsQCatEquivalence (relativeFunctorOverPre pointedSpaceProjection e.hom) :=
    (qCatEquivalenceOfIso ep).isQCatEquivalence
  have hg : (Over.map F).map g ≫ e.hom =
      Over.homMk (U := Over.mk (((SSet.uliftFunctor.{u + 1, u}).map D) ≫ F))
        (V := Over.mk (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)).val)
        (joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))
        (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)).property := by
    apply Over.OverMorphism.ext
    exact uliftConeShapeIso_inr K 0
  rw [leftFibrationConeRestriction_eq_overPre, ← hg, relativeFunctorOverPre_comp]
  exact he.comp h

/-- 元の Yoneda の元の極限錐の像は、実際の全錐の一点からの切断制限を同値にする。 -/
lemma representableNativeConePointedRestriction_isQCatEquivalence
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) (y : C _⦋0⦌) :
    IsQCatEquivalence (coneSectionRestriction
      (mapJoinCone (representablePresheafInfinity y) (JoinCone.ulift.{u, u + 1} c))
      pointSpaceVertex) :=
  coherentPointedRestriction_nativeCone_isQCatEquivalence c (representablePresheafInfinity y)
    (representablePointedConeRestriction_isQCatEquivalence c hc y)

end SerrePositivity.InfinityCategories.HomotopyLimits
