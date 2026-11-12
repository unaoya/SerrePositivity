module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：固定した辺に沿う coslice の前合成を全パラメータで作り、底を指定して持ち上げる。
方針：終点への制限と相対終点制限の自明 Kan fibration 性から切断を選ぶ。
規約：前合成の選択には厳密な終点評価を持たせる。相対持ち上げでは底の余錐全体を固定する。
使われ方：部分余極限の Hom 比較と、比較辺による後合成の高次の自然性。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
noncomputable section

/-- 固定辺の終点側の余錐を、辺全体の余錐へ延長する切断。 -/
def cosliceEdgeSection {X : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_target_trivialKanFibration e
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)))).choose

/-- 選んだ辺の延長の終点側は、元の余錐の族を厳密に再現する。 -/
lemma cosliceEdgeSection_target {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    cosliceEdgeSection e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = 𝟙 _ := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_target_trivialKanFibration e
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)))).choose_spec

/-- 固定した実際の辺に沿う、coslice 全体の前合成。 -/
def cosliceEdgePrecomposition {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 2) ≫ e) :=
  cosliceEdgeSection e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (1 : Fin 2))

/-- 辺による前合成は、余錐の可変な終点の全単体を保つ。 -/
lemma cosliceEdgePrecomposition_projection {X : SSet.{u}} [Quasicategory X]
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    cosliceEdgePrecomposition e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (1 : Fin 2) ≫ e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  rw [cosliceEdgePrecomposition, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2)),
    ← Category.assoc, cosliceEdgeSection_target, Category.id_comp]

/-- inner fibration の固定辺から終点への相対 coslice 制限も自明 Kan fibration。 -/
lemma relativeCosliceRestriction_target_trivialKanFibration {E B : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction e q (stdSimplex.δ (0 : Fin 2))) := by
  let A : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face {(0 : Fin 2)}ᶜ
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A.ι := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom,
      stdSimplex.faceSingletonComplIso_hom_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceMap_trivialKanFibration_of_rightAnodyne e q A hA
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeCosliceRestriction_trivialKanFibration_subcomplexIso e q A
    (stdSimplex.faceSingletonComplIso (0 : Fin 2))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

/-- 指定した底の合成三角形の族を、終点側の族を保って全空間へ持ち上げる。 -/
lemma exists_relativeEdgeCosliceLift {E B T : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))
    (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (e ≫ q))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2))) :
    ∃ l : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e,
      l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = a ∧
        l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q = b := by
  have := relativeCosliceRestriction_target_trivialKanFibration e q
  let v := pullback.lift a b h
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction e q (stdSimplex.δ (0 : Fin 2)))
  refine ⟨v ≫ s, ?_, ?_⟩
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.fst _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_fst, Category.id_comp, v] using ht
  · have ht := congrArg (fun z ↦ v ≫ z ≫ pullback.snd _ _) hs
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.relativeCosliceRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.squareComparison, Category.assoc,
      pullback.lift_snd, Category.id_comp, v] using ht

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
