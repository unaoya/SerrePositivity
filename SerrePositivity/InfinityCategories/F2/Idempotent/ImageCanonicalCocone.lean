module

public import SerrePositivity.InfinityCategories.F1B.Idempotent.IdemImageKanShape
public import SerrePositivity.InfinityCategories.F1B.Idempotent.WalkingJoinCones
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.LeftCanonicalCocone

/-!
概要：元の分裂対象での標準左 Kan 余錐を、保存済みの同じ Idem 余錐と照合する。
方針：元の comma の構造射は全て元の射影であり、全余錐の nerve 比較を使う。
規約：元の全余錐そのものの等式を証明し、脚のホモトピー類だけで代用しない。
使われ方：元の全強分裂図式が、元の Idem 包含に沿う左 Kan 延長であること。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂対象での通常の標準余錐は、元の Idem 余錐の同じ射影への制限。 -/
lemma walkingImageCanonicalCocone_eq :
    SerrePositivity.InfinityCategories.F1B.classicalLeftKanCanonicalCocone walkingInclusion (𝟭 WalkingSplit.{u}) walkingImage =
      walkingCocone.whisker (CostructuredArrow.proj walkingInclusion walkingImage) := by
  have h : (SerrePositivity.InfinityCategories.F1B.classicalLeftKanCanonicalCocone
      walkingInclusion (𝟭 WalkingSplit.{u}) walkingImage).ι =
        (walkingCocone.whisker (CostructuredArrow.proj walkingInclusion walkingImage)).ι := by
    apply NatTrans.ext
    funext c
    exact walkingHom_to_image c.hom
  exact congrArg (Cocone.mk walkingImage) h

/-- 元の native 標準余錐は、保存済みの同じ Idem 余錐を元の左局所射影で制限したもの。 -/
lemma idemImageCanonicalCocone_eq :
    (leftKanCanonicalCocone idemInclusion (𝟙 SplitShape.{u}) (nerveVertex walkingImage)).val =
      joinMap (leftKanProjection idemInclusion (nerveVertex walkingImage))
        (𝟙 (Δ[0] : SSet.{u})) ≫ walkingJoinCocone.val := by
  let e := SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso walkingInclusion walkingImage.{u}
  apply (cancel_epi (joinMap e.hom (𝟙 (Δ[0] : SSet.{u})))).mp
  have hc := SerrePositivity.InfinityCategories.F1B.nerveLeftKanCanonicalCocone walkingInclusion
    (𝟭 WalkingSplit.{u}) walkingImage
  have hw := congrArg (fun c ↦ (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv c).val) walkingImageCanonicalCocone_eq
  have hr := SerrePositivity.InfinityCategories.F1B.nerveCocone_whisker walkingCocone
    (CostructuredArrow.proj walkingInclusion walkingImage)
  have hp : e.hom ≫ leftKanProjection idemInclusion (nerveVertex walkingImage) =
      nerveMap (CostructuredArrow.proj walkingInclusion walkingImage) :=
    SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso_hom_projection walkingInclusion walkingImage
  have hj : joinMap e.hom (𝟙 (Δ[0] : SSet.{u})) ≫
      joinMap (leftKanProjection idemInclusion (nerveVertex walkingImage)) (𝟙 Δ[0]) =
        joinMap (nerveMap (CostructuredArrow.proj walkingInclusion walkingImage)) (𝟙 Δ[0]) :=
    (joinMap_comp _ _ _ _).symm.trans (congrArg₂ joinMap hp (Category.id_comp _))
  exact hc.trans (hw.trans (hr.symm.trans
    ((congrArg (fun f ↦ f ≫ walkingJoinCocone.val) hj).symm.trans (Category.assoc _ _ _))))

end SerrePositivity.InfinityCategories.F2.Idempotent
