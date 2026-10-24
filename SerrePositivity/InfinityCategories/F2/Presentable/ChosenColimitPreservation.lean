module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitEvaluation
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftHomUniversal

/-!
概要：元の指定余極限の保存は選んだ全余極限比較の可逆性に同値。
方針：全余錐比較を各図式で評価し、元の余極限余錐の一意性を使う。
規約：選んだ全比較自身について判定する。
使われ方：有限余積保存を Yoneda 生成対象で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の形状の余極限を保てば指定した全余極限比較は可逆。
方針：全図式の点ごとの普遍余錐の像を使い、比較の成分を可逆とする。
規約：同じ全比較を使う。
使われ方：保存判定の必要条件。 -/
lemma chosenColimitComparison_isIso_of_preservation
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, HasColimit p) (hY : ∀ p : K ⟶ Y, HasColimit p) (q : X ⟶ Y)
    (h : ∀ (p : K ⟶ X) (c : JoinCocone p), IsColimitCone c →
      IsColimitCone (mapJoinCocone q c)) : IsIso (chosenColimitComparison hX hY q) := by
  apply F1B.kanFunctorHom_isIso_of_components
  intro a
  apply chosenColimitComparison_evaluate_isIso hX hY q a
  apply (isColimitCone_iff_of_cocone_val_eq _ _
    (chosenColimitImageCocone_evaluate_val hX (𝟙 ((ihom K).obj X)) q a)).mpr
  exact h _ _ (chosenColimitParameterCocone_isPointwiseColimit hX (𝟙 ((ihom K).obj X)) a)

/-- 概要：指定した全比較が可逆なら元の形状の全余極限を保存する。
方針：全比較を指定図式で評価し、選んだ余錐から元の余錐へ同型で戻す。
規約：元の指定余錐の像を結論に保持する。
使われ方：生成対象での比較から有限余積保存へ戻す。 -/
lemma chosenColimit_preservation_of_comparison_isIso
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, HasColimit p) (hY : ∀ p : K ⟶ Y, HasColimit p) (q : X ⟶ Y)
    (h : IsIso (chosenColimitComparison hX hY q))
    (p : K ⟶ X) (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone q c) := by
  have hi := chosenColimitImageCocone_evaluate_isColimit hX hY q (functorVertex p)
    (functorHomEvaluate_isIso (chosenColimitComparison hX hY q) (functorVertex p))
  have hv : (evaluateFunctorCocone
      (chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) (functorVertex p)).val =
      (mapJoinCocone q (chosenColimitCocone K X hX p)).val := by
    rw [chosenColimitImageCocone_evaluate_val]
    change (evaluateFunctorCocone (chosenColimitParameterCocone hX (𝟙 ((ihom K).obj X)))
      (functorVertex p)).val ≫ q = (chosenColimitCocone K X hX p).val ≫ q
    rw [chosenColimitParameterCocone_id_evaluate_val]
  have hj := (isColimitCone_iff_of_cocone_val_eq _ _ hv).mp hi
  exact hj.of_vertexIso ((hoFunctor.map (sliceUnderPostcomp p q)).toFunctor.mapIso
    (colimitConeIso (chosenColimitCocone K X hX p) c
      (chosenColimitCocone_isColimit K X hX p) hc))

/-- 概要：元の形状の全余極限保存は指定した全比較の可逆性に同値。
方針：二つの構成済みの方向を組み合わせる。
規約：選んだ全比較を固定する。
使われ方：有限余積の全比較による公開判定。 -/
lemma chosenColimitComparison_isIso_iff_preservation
    {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (hX : ∀ p : K ⟶ X, HasColimit p) (hY : ∀ p : K ⟶ Y, HasColimit p) (q : X ⟶ Y) :
    IsIso (chosenColimitComparison hX hY q) ↔
      ∀ (p : K ⟶ X) (c : JoinCocone p), IsColimitCone c →
        IsColimitCone (mapJoinCocone q c) :=
  ⟨chosenColimit_preservation_of_comparison_isIso hX hY q,
    chosenColimitComparison_isIso_of_preservation hX hY q⟩

end SerrePositivity.InfinityCategories.F2.Presentable
