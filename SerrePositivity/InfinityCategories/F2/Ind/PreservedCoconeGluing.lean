module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedConeSpanTransfer
public import SerrePositivity.InfinityCategories.F1.Joins.ConeSpanCoconeGlue

/-!
概要：共通の保存された余極限を付加し、二つの全余錐を像の普遍性ごと貼る。
方針：元の pushout の全射の等式を後合成し、同じ全余錐の像を比較する。
規約：指定した二つの余錐やその頂点を選び直さない。
使われ方：I-2 d′ の全有限形状の保存性帰納の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 保存された共通余極限の付加は、同じ元の図式の余極限保存と同値。 -/
lemma hasPreservedColimit_commonDiagram_iff {A B X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {p : A ⟶ X}
    (G : X ⟶ Y) (a : JoinCocone p) (ha : IsColimitCone a)
    (hGa : IsColimitCone (mapJoinCocone G a)) (f : A ⟶ B) (F : B ⟶ X)
    (hf : f ≫ F = p) :
    HasPreservedColimit G (commonColimitDiagram a f F hf) ↔ HasPreservedColimit G F := by
  have h := hasPreservedColimit_iff_colimit_attachment G a ha hGa f
    (pushout.inr f (joinInl A Δ[0])) (pushout.inl f (joinInl A Δ[0]))
    (IsPushout.of_hasPushout f (joinInl A Δ[0])).flip
    (commonColimitDiagram a f F hf) (commonColimitDiagram_cone a f F hf)
  simpa only [commonColimitDiagram_base] using h

variable {A B C X Y : SSet.{u}} [Quasicategory Y]
  (G : X ⟶ Y) (i : A ⟶ B) (j : A ⟶ C)
  {p : B ⟶ X} {q : C ⟶ X} (b : JoinCocone p) (c : JoinCocone q)
  (he : i ≫ p = j ≫ q)

/-- 貼り合わせの左側の元の全余錐の像も、元の左余錐の像と同じ。 -/
lemma coneSpanCoconeGlue_left_map_isColimit
    (hb : IsColimitCone (mapJoinCocone G b)) :
    IsColimitCone (mapJoinCocone G
      (coneSpanLeftCocone i j (coneSpanCoconeGlue i j b c he))) := by
  apply (isColimitCone_iff_of_sameMap _ (mapJoinCocone G b) ?_).mpr hb
  change (coneSpanLeftCocone i j (coneSpanCoconeGlue i j b c he)).val ≫ G = b.val ≫ G
  exact congrArg (· ≫ G) (coneSpanCoconeGlue_left i j b c he)

/-- 貼り合わせの右側の元の全余錐の像も、元の右余錐の像と同じ。 -/
lemma coneSpanCoconeGlue_right_map_isColimit
    (hc : IsColimitCone (mapJoinCocone G c)) :
    IsColimitCone (mapJoinCocone G
      (coneSpanRightCocone i j (coneSpanCoconeGlue i j b c he))) := by
  apply (isColimitCone_iff_of_sameMap _ (mapJoinCocone G c) ?_).mpr hc
  change (coneSpanRightCocone i j (coneSpanCoconeGlue i j b c he)).val ≫ G = c.val ≫ G
  exact congrArg (· ≫ G) (coneSpanCoconeGlue_right i j b c he)

end SerrePositivity.InfinityCategories.F2.Ind
