module

public import SerrePositivity.InfinityCategories.F2.Presentable.InitialBoundaryHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.PostcompositionAdjunction
public import SerrePositivity.InfinityCategories.F1B.Cones.ColimitConstantFamily
public import SerrePositivity.InfinityCategories.F1.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.F1.Joins.JoinQuasicategory

/-!
概要：左随伴は quasicategory 形状の元の指定余極限余錐を保存する。
方針：定値パラメータ族の余極限の射の制限を、全自然な adjunct 対応で移す。
規約：標的の余完備性を入力にせず、同じ指定余錐像を判定する。
使われ方：専用反映を小余積と幾何学的実現へ適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：左随伴は元の指定 quasicategory 形状の余極限を保存する。
方針：各定値パラメータ族の射の制限を随伴の自然な Hom 全単射で比較する。
規約：同じ全余錐を保持し、図式の置換を要求しない。
使われ方：反映した bar の各項と実現の余極限性。 -/
lemma mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    {K X Y : SSet.{u}} [Quasicategory K] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone F c) := by
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction
  apply initialBoundaryLifting_pre_of_constantFamilyHom
  intro A T
  let aA := postcompositionAdjunction a A
  let δ := joinInl K (Δ[0] : SSet.{u})
  let H := c.val ≫ constantFunctorMap A X
  let V := T ≫ constantFunctorMap A Y
  let R := (hoFunctor.map ((pre δ).app ((ihom A).obj X))).toFunctor
  let S := (hoFunctor.map ((pre δ).app ((ihom A).obj Y))).toFunctor
  have hsource : Function.Bijective (R.map :
      FunctorHom H (V ≫ (ihom A).map G) → _) :=
    homMap_bijective_of_initialBoundaryLifting ((pre δ).app ((ihom A).obj X))
      (functorVertex H) (F1B.isColimitCone_constantFamily c hc).initialBoundaryLifting
      (functorVertex (V ≫ (ihom A).map G))
  let e := aA.homEquiv H V
  let e' := aA.homEquiv (δ ≫ H) (δ ≫ V)
  have he : (fun α : FunctorHom (H ≫ (ihom A).map F) V ↦ e' (S.map α)) =
      (fun α ↦ R.map (e α)) := by
    funext α
    exact aA.homEquiv_precomp δ H V α
  have hb : Function.Bijective (fun α : FunctorHom (H ≫ (ihom A).map F) V ↦
      e' (S.map α)) := by
    rw [he]
    exact hsource.comp e.bijective
  have hH : H ≫ (ihom A).map F = (mapJoinCocone F c).val ≫ constantFunctorMap A Y := by
    dsimp only [H, mapJoinCocone]
    rw [Category.assoc, constantFunctorMap_postcomp, ← Category.assoc]
  change Function.Bijective (S.map :
    FunctorHom ((mapJoinCocone F c).val ≫ constantFunctorMap A Y) V → _)
  rw [← hH]
  exact hb.of_comp_left e'.injective

end SerrePositivity.InfinityCategories.F2.Presentable
