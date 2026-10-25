module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitRestriction
public import SerrePositivity.InfinityCategories.F1.Joins.CommonColimitAttachment

/-!
概要：保存された部分余極限の付加は、残りの全余極限の保存性を保ち反映する。
方針：元の圏と像の圏の両側で余錐制限を自明 Kan fibration として使う。
規約：元の指定部分余錐とその同じ像を固定する。
使われ方：I-2 d′ の形状 pushout 帰納の共通頂点の付加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ指定部分余極限が保存されれば、その付加は全余極限の保存性を変えない。 -/
lemma hasPreservedColimit_iff_colimit_attachment
    {A B D X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {p : A ⟶ X} (G : X ⟶ Y) (c : JoinCocone p) (hc : IsColimitCone c)
    (hGc : IsColimitCone (mapJoinCocone G c))
    (i : A ⟶ B) (j : join A Δ[0] ⟶ D) (k : B ⟶ D)
    (hp : IsPushout (joinInl A Δ[0]) i j k) (F : D ⟶ X) (hj : j ≫ F = c.val) :
    HasPreservedColimit G F ↔ HasPreservedColimit G (k ≫ F) := by
  have hjG : j ≫ (F ≫ G) = (mapJoinCocone G c).val := by
    rw [← Category.assoc, hj]
    rfl
  have := cosliceRestriction_trivialKanFibration_of_colimit_attachment c hc i j k hp F hj
  have := cosliceRestriction_trivialKanFibration_of_colimit_attachment
    (mapJoinCocone G c) hGc i j k hp (F ≫ G) hjG
  exact hasPreservedColimit_iff_nativeRestriction F k G
    (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict F k)).isQCatEquivalence
    (qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict (F ≫ G) k)).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
