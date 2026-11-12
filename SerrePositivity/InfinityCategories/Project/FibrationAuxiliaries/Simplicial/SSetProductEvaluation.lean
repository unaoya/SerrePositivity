module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity

/-!
概要：単体集合の直積への持ち上げと定値射を、各次数・零単体で評価する。
方針：二射影の普遍性と零単体の唯一の自己射を使う。
規約：選択した極限円錐を展開せず、元の二射を保持する。
使われ方：二変数 Hom 関手の同じ制限の値の計算。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 単体集合の直積への持ち上げを各次数で評価すると、二成分の評価の組。 -/
lemma ssetLift_apply {A B T : SSet.{u}} (f : T ⟶ A) (g : T ⟶ B)
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (lift f g).app n x = (f.app n x, g.app n x) := by
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (lift_fst f g) n) x
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (lift_snd f g) n) x

/-- 指定零単体への定値射を零単体で評価すると、その同じ指定零単体。 -/
lemma ssetConst_zero_apply {A B : SSet.{u}} (b : B _⦋0⦌) (a : A _⦋0⦌) :
    (SSet.const b).app (Opposite.op ⦋0⦌) a = b := by
  change B.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op b = b
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h]
  change B.map (𝟙 (Opposite.op ⦋0⦌)) b = b
  exact CategoryTheory.Functor.map_id_apply B (Opposite.op ⦋0⦌) b

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
