module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.EvaluationChartNaturality
/-!
概要：元の評価チャートは、同じ bar ホモロジー余錐の全ての脚と可換する。
方針：元の実脚の自然性を同じ頂点表示へ運び、H⁰ 対象同型を相殺する。
規約：元の実 bar 余錐そのものを使う。
使われ方：filtered 空間の五条件と c2 の無条件化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : Type u} [PartialOrder I]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve I) ⟶ dgProjectiveModuleNerve R D)
  (c : JoinCocone G) (x : D)

lemma dgBarCompactEvaluationPiChart_leg (n : ℕ) (i : I) :
    DGBarCompactPiChartNaturality
      (dgBarCompactEvaluationStagePiChart R D G x n i)
      (dgBarCompactEvaluationApexPiChart R D G c x n)
      (dgBarCompactSpaceLeg (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x) i)
      ((dgBarCompactEvaluationCoefficientCocone R D G c x (n + 1)).ι.app i).hom := by
  have hn := (dgBarCompactEvaluationVertexPiChart_naturality R D x
    (dgBarCompactEvaluationLegEdge R D G c i) n).cast rfl
      (dgBarCompactEvaluationApexSpace_eq R D G c x)
  rw [dgBarCompactEvaluationLeg_eq] at hn
  exact hn.reparam_source
    (dgBarCompactEvaluationStageHomologyIso R D G x (-((n + 1 : ℕ) : ℤ)) i).symm.toLinearEquiv.toEquiv
    ((dgBarCompactEvaluationCoefficientCocone R D G c x (n + 1)).ι.app i).hom
    (fun a => (ConcreteCategory.congr_hom
      (dgBarCompactEvaluationHomologyLeg R D G c x (-((n + 1 : ℕ) : ℤ)) i) a).symm)

set_option maxHeartbeats 1000000 in
lemma dgBarCompactEvaluationPiZeroChart_leg (i : I) :
    DGBarCompactPiZeroChartNaturality
      (dgBarCompactEvaluationStagePiZeroChart R D G x i)
      (dgBarCompactEvaluationApexPiZeroChart R D G c x)
      (dgBarCompactSpaceLeg (dgBarCompactEvaluationPosetDiagram R D G x)
        (dgBarCompactEvaluationCocone R D G c x) i)
      ((dgBarCompactEvaluationCoefficientCocone R D G c x 0).ι.app i).hom := by
  have hr : DGBarCompactPiZeroChartNaturality
      (dgBarCompactEvaluationVertexPiZeroChart R D x (dgBarCompactEvaluationStageVertex R D G i))
      (dgBarCompactEvaluationVertexPiZeroChart R D x c.vertex)
      (dgBarCompactEvaluationEdgeValue R D x (dgBarCompactEvaluationLegEdge R D G c i)) _ :=
    ⟨dgBarCompactEvaluationVertexPiZeroChart_naturality R D x
      (dgBarCompactEvaluationLegEdge R D G c i)⟩
  have hn := hr.cast rfl (dgBarCompactEvaluationApexSpace_eq R D G c x)
  rw [dgBarCompactEvaluationLeg_eq] at hn
  exact hn.reparam_source
    (dgBarCompactEvaluationStageHomologyIso R D G x 0 i).symm.toLinearEquiv.toEquiv
    ((dgBarCompactEvaluationCoefficientCocone R D G c x 0).ι.app i).hom
    (fun a => (ConcreteCategory.congr_hom (dgBarCompactEvaluationHomologyLeg R D G c x 0 i) a).symm)

end SerrePositivity.InfinityCategories
