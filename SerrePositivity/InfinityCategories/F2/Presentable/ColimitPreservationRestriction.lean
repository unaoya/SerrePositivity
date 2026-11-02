module

public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalColimitExistence
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：全余錐の制限同値に沿って指定余極限の保存を移す。
方針：制限同値で余錐を持ち上げ、同じ後合成が写す頂点同型で戻す。
規約：元の指定余錐の像の余極限性を結論する。
使われ方：bar 展開による小余極限保存判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：両標的の全余錐制限が同値なら展開図式の保存から元の図式の保存を得る。
方針：指定余錐の前像を選び、同じ後合成による同型で指定像へ戻す。
規約：余極限の存在だけへ弱めない。
使われ方：全単体や comma 添字から元の余極限への帰還。 -/
lemma colimitPreservation_of_restrictionEquivalences
    {A B X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (i : A ⟶ B) (H : B ⟶ X) (U : X ⟶ Y)
    (hX : IsQCatEquivalence (sliceUnderRestrict H i))
    (hY : IsQCatEquivalence (sliceUnderRestrict (H ≫ U) i))
    (hU : ∀ c : JoinCocone H, IsColimitCone c → IsColimitCone (mapJoinCocone U c))
    (d : JoinCocone (i ≫ H)) (hd : IsColimitCone d) :
    IsColimitCone (mapJoinCocone U d) := by
  obtain ⟨c, ⟨e⟩⟩ := hX.choose.isEssentiallySurjective d
  have hc : IsColimitCone c :=
    (hX.choose.isInitialVertex_iff c).mpr (hd.of_vertexIso e.symm)
  have hr := (hY.choose.isInitialVertex_iff (mapJoinCocone U c)).mp (hU c hc)
  have em := VertexIso.map e (sliceUnderPostcomp (i ≫ H) U)
  exact hr.of_vertexIso em

end SerrePositivity.InfinityCategories.F2.Presentable
