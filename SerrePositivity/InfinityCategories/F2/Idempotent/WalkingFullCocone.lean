module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingJoinCones
public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingImageUniversal

/-!
概要：元の全分裂添字の恒等図式に、元の分裂対象を頂点とする全余錐を付ける。
方針：全ての元の対象に吸収射の脚を付け、元の冪等包含への制限を照合する。
規約：制限後の余錐は、保存済みの元の Idem の余錐そのもの。
使われ方：任意の強い分裂図式の像の元の余極限余錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全分裂添字の恒等図式から、元の分裂対象への全余錐。 -/
def walkingFullCocone : Cocone (𝟭 WalkingSplit.{u}) where
  pt := walkingImage
  ι :=
    { app P := walkingAbsorbingHom P walkingImage
      naturality _ _ f := by
        change f ≫ walkingAbsorbingHom _ _ = _ ≫ 𝟙 _
        rw [comp_walkingAbsorbingHom, Category.comp_id]
        rfl }

/-- 元の全分裂添字の恒等図式への native な全余錐。 -/
def walkingFullJoinCocone : JoinCocone (𝟙 SplitShape.{u}) :=
  SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv walkingFullCocone

/-- 元の全余錐の点側への制限は、元の分裂対象の包含。 -/
lemma walkingFullJoinCocone_point :
    joinInr SplitShape (Δ[0] : SSet.{u}) ≫ walkingFullJoinCocone.val = nervePoint walkingImage :=
  SerrePositivity.InfinityCategories.F1B.nerveCocone_point walkingFullCocone

/-- 元の冪等包含へ制限した全余錐は、元の Idem の余錐そのもの。 -/
lemma walkingFullJoinCocone_restrict :
    joinMap idemInclusion (𝟙 (Δ[0] : SSet.{u})) ≫ walkingFullJoinCocone.val =
      walkingJoinCocone.val :=
  SerrePositivity.InfinityCategories.F1B.nerveCocone_whisker walkingFullCocone walkingInclusion

/-- 元の分裂対象での全余錐の脚は、その元の恒等辺。 -/
lemma walkingFullJoinCocone_image_leg :
    walkingFullJoinCocone.{u}.val.app (Opposite.op ⦋1⦌)
      (SerrePositivity.InfinityCategories.F1B.joinCoconeLegSimplex (nerveVertex walkingImage)) =
        ComposableArrows.mk₁ (𝟙 walkingImage) :=
  SerrePositivity.InfinityCategories.F1B.nerveCocone_leg walkingFullCocone walkingImage

end SerrePositivity.InfinityCategories.F2.Idempotent
