module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedConePointedRestriction

/-!
概要：像の native 全錐の pointed 制限の同値性を、元の持ち上げた全錐の制限へ反映する。
方針：元の join の宇宙同型による前合成を、同じ可換三角形で消去する。
規約：元の全錐と脚を保持し、頂点の比較だけへ弱めない。
使われ方：表現可能関手による極限の検出の反映側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 像の同じ native 全錐の制限が同値なら、元の pointed 制限も同値。 -/
lemma coherentPointedRestriction_of_nativeCone_isQCatEquivalence
    {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (h : IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
      (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)))) :
    IsQCatEquivalence (coherentPointedRestriction F
      (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
        (joinInr (Δ[0] : SSet.{u}) K) c.property)) := by
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
  rw [leftFibrationConeRestriction_eq_overPre, ← hg, relativeFunctorOverPre_comp] at h
  exact he.cancel_left h

end SerrePositivity.InfinityCategories
