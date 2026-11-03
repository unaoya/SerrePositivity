module

public import SerrePositivity.InfinityCategories.F1B.Idempotent.WalkingJoinCones
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingImageUniversal
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.ConeNaturality

/-!
概要：元の全分裂添字の恒等図式に、元の分裂対象を頂点とする全錐を付ける。
方針：全ての元の対象へ吸収射の脚を出し、元の冪等包含への制限を照合する。
規約：制限後の錐は、保存済みの元の Idem の錐そのもの。
使われ方：任意の強い分裂図式の像の元の極限錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂対象から元の全分裂添字の恒等図式への全錐。 -/
def walkingFullCone : Cone (𝟭 WalkingSplit.{u}) where
  pt := walkingImage
  π :=
    { app P := walkingAbsorbingHom walkingImage P
      naturality _ _ f := by
        change 𝟙 walkingImage ≫ walkingAbsorbingHom _ _ = walkingAbsorbingHom _ _ ≫ f
        exact (Category.id_comp _).trans (walkingAbsorbingHom_comp f).symm }

/-- 元の全分裂添字の恒等図式への native な全錐。 -/
def walkingFullJoinCone : JoinCone (𝟙 SplitShape.{u}) := SerrePositivity.InfinityCategories.F1B.nerveCone walkingFullCone

/-- 元の全錐の点側への制限は、元の分裂対象の包含。 -/
lemma walkingFullJoinCone_point :
    joinInl (Δ[0] : SSet.{u}) SplitShape ≫ walkingFullJoinCone.val = nervePoint walkingImage := by
  apply SSet.yonedaEquiv.injective
  exact (SerrePositivity.InfinityCategories.F1B.nerveCone_vertex walkingFullCone).trans
    (SSet.yonedaEquiv.apply_symm_apply (nerveVertex walkingImage)).symm

/-- 元の冪等包含へ制限した全錐は、元の Idem の錐そのもの。 -/
lemma walkingFullJoinCone_restrict :
    joinMap (𝟙 (Δ[0] : SSet.{u})) idemInclusion ≫ walkingFullJoinCone.val =
      walkingJoinCone.val :=
  SerrePositivity.InfinityCategories.F1B.nerveCone_whisker walkingFullCone walkingInclusion

/-- 元の分裂対象での全錐の脚は、その元の恒等辺。 -/
lemma walkingFullJoinCone_image_leg :
    walkingFullJoinCone.{u}.val.app (Opposite.op ⦋1⦌) (SerrePositivity.InfinityCategories.F1B.coneLegSimplex walkingImage) =
      ComposableArrows.mk₁ (𝟙 walkingImage) :=
  SerrePositivity.InfinityCategories.F1B.nerveCone_leg walkingFullCone walkingImage

end SerrePositivity.InfinityCategories.F2.Idempotent
