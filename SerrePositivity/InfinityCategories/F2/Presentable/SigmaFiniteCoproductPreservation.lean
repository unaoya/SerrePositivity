module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaYonedaFamilyCoproductComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitFilteredGeometric
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteCoproductSiftedPreservation

/-!
概要：P_Σ 全体の有限余積保存を元の Yoneda 制限上の有限余積保存へ縮約する。
方針：指定した全有限余積比較を元の Yoneda 像で検査し、有限座標の生成で可逆にする。
規約：元の指定比較と元の小さい底を保持する。
使われ方：全小余極限保存判定の有限条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：Yoneda 制限の有限余積保存から、P_Σ の指定した有限余積比較は可逆。
方針：両側の filtered・実現保存と、元の Yoneda 有限図式での比較を使う。
規約：元の全関手比較自身を検出する。
使われ方：全有限余積保存の構成。 -/
lemma sigmaFiniteCoproductComparison_isIso
    {I : Type u} [Finite I] {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : ∀ p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D, HasColimit p)
    (G : SigmaPresheafInfinity C ⟶ D)
    (hGf : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hGg : PreservesSmallGeometricRealizations G)
    (hG : PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G)) :
    IsIso (chosenColimitComparison (sigma_hasSmallColimits hC (nerve (Discrete I))) hD G) := by
  let hX := sigma_hasSmallColimits hC
  let hK := hX (nerve (Discrete I))
  apply sigmaFiniteFamilyComparison_isIso hC
    (preservesSmallFilteredColimits_comp (postcomposition_preservesSmallFiltered hX G hGf)
      (chosenColimitFunctor_preservesSmallFiltered hD))
    (preservesSmallFilteredColimits_comp (chosenColimitFunctor_preservesSmallFiltered hK) hGf)
    (preservesSmallGeometricRealizations_comp (postcomposition_preservesSmallGeometric hX G hGg)
      (chosenColimitFunctor_preservesSmallGeometric hD))
    (preservesSmallGeometricRealizations_comp (chosenColimitFunctor_preservesSmallGeometric hK) hGg)
  exact sigmaYonedaFamily_colimitComparison_isIso hC hD G hG

/-- 概要：filtered・実現保存関手の Yoneda 制限が有限余積を保てば全有限余積を保つ。
方針：元の全有限余積比較の可逆性を元の指定余錐の保存へ戻す。
規約：空添字と元の全余錐を保持する。
使われ方：全小余極限保存判定の十分条件。 -/
lemma sigma_preservesFiniteCoproducts_of_yoneda
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : ∀ (I : Type u) [Finite I]
      (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D), HasColimit p)
    (G : SigmaPresheafInfinity C ⟶ D)
    (hGf : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hGg : PreservesSmallGeometricRealizations G)
    (hG : PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G)) :
    PreservesFiniteCoproducts G := by
  intro I hI p c hc
  exact chosenColimit_preservation_of_comparison_isIso
    (sigma_hasSmallColimits hC (nerve (Discrete I))) (hD I) G
    (sigmaFiniteCoproductComparison_isIso hC (hD I) G hGf hGg hG) p c hc

/-- 概要：P_Σ 全体での有限余積保存は元の Yoneda 制限へ移る。
方針：元の Yoneda が保つ同じ普遍余錐を順に写す。
規約：元の小さい底の全余錐を使う。
使われ方：全小余極限保存判定の必要条件。 -/
lemma sigma_yoneda_preservesFiniteCoproductsOnBase
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (G : SigmaPresheafInfinity C ⟶ D) (hG : PreservesFiniteCoproducts G) :
    PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G) := by
  intro I hI p c hc
  have h := hG I _ _ (sigmaYoneda_finiteCoproduct_isColimit c hc)
  exact (isColimitCone_iff_of_cocone_val_eq _ _
    (Category.assoc (JoinCocone.ulift.{u, u + 1} c).val (sigmaYonedaInfinityMap C) G).symm).mpr h

/-- 概要：filtered・実現保存関手の有限余積保存は元の Yoneda 制限上で判定できる。
方針：構成済みの両方向を組み合わせる。
規約：有限条件は元の小さい底だけに課す。
使われ方：P_Σ の全小余極限保存判定。 -/
lemma sigma_preservesFiniteCoproducts_iff_yoneda
    {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : ∀ (I : Type u) [Finite I]
      (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D), HasColimit p)
    (G : SigmaPresheafInfinity C ⟶ D)
    (hGf : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hGg : PreservesSmallGeometricRealizations G) :
    PreservesFiniteCoproducts G ↔
      PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G) :=
  ⟨sigma_yoneda_preservesFiniteCoproductsOnBase G,
    sigma_preservesFiniteCoproducts_of_yoneda hC hD G hGf hGg⟩

end SerrePositivity.InfinityCategories.F2.Presentable
