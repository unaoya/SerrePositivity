module

public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteDiagramReconstruction
public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitComparisonAtDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteCoproductsOnBase
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSmallColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport

/-!
概要：全成分が元の Yoneda 像の有限図式では、有限余積比較が可逆になる。
方針：元の小さい底の実際の有限余積へ戻し、同じ普遍余錐の像で比較する。
規約：有限余積条件は元の Yoneda 制限上だけに課す。
使われ方：全有限余積比較の可逆性の生成対象での基準条件。
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

/-- 概要：元の Yoneda 像からなる有限図式の指定比較は制限の有限余積保存で可逆。
方針：小さい底の有限余積の像と選んだ普遍余錐を同じ coslice の同型で比較する。
規約：元の全関手比較自身について結論する。
使われ方：有限座標による生成表示の基準図式。 -/
lemma sigmaYonedaFamily_colimitComparison_isIso
    {I : Type u} [Finite I] {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    (hD : ∀ p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ D, HasColimit p)
    (G : SigmaPresheafInfinity C ⟶ D)
    (hG : PreservesFiniteCoproductsOnBase (sigmaYonedaInfinityMap C ≫ G))
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ SigmaPresheafInfinity C)
    (hp : IsSigmaYonedaFamilyOutside C ∅ p) :
    IsIso (functorHomEvaluate
      (chosenColimitComparison (sigma_hasSmallColimits hC (nerve (Discrete I))) hD G)
      (functorVertex p)) := by
  obtain ⟨q, hq⟩ := sigmaYonedaFamily_factorization p hp
  obtain ⟨c, hc⟩ := hasFiniteCoproducts_of_op_finiteProducts hC q
  let d := coherentCoconeOfDiagramEq hq
    (mapJoinCocone (sigmaYonedaInfinityMap C) (JoinCocone.ulift.{u, u + 1} c))
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff hq _).mp
    (sigmaYoneda_finiteCoproduct_isColimit c hc)
  have hdG : IsColimitCone (mapJoinCocone G d) := by
    have hv : (mapJoinCocone G d).val =
        (mapJoinCocone (sigmaYonedaInfinityMap C ≫ G) (JoinCocone.ulift.{u, u + 1} c)).val := by
      change (coherentCoconeOfDiagramEq hq _).val ≫ G = _
      rw [coherentCoconeOfDiagramEq_val]
      rfl
    exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr (hG I q c hc)
  apply chosenColimitComparison_isIso_at_diagram
  exact hdG.of_vertexIso ((hoFunctor.map (sliceUnderPostcomp p G)).toFunctor.mapIso
    (colimitConeIso d _ hd (chosenColimitCocone_isColimit _ _ _ p)))

end SerrePositivity.InfinityCategories.F2.Presentable
