module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparisonEdgeComposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorPrecompositionComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationNaturalTransport

/-!
概要：底の三角形に沿う全 left fibrations 上の transport の合成則。
方針：三角形上の全切断の始点評価で比較し、始点の大域的同型を消去する。
規約：構成済みの transport の辺そのものを三辺として使う。
使われ方：一般の底上の共同評価の二単体の構成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：切断制限と頂点評価の合成は像の頂点での評価と豊穣比較として一致する。
方針：各対象の全切断空間上の厳密な可換式を使う。
規約：全対象と全高次の相対射について同時に成立。
使われ方：大域的な比較の合成則を切断評価へ適用する。 -/
lemma relativeFunctorPrecompositionComparison_trans_evaluate {A D B : SSet.{u}}
    (a : A ⟶ B) (i : D ⟶ A) (v : D _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPrecompositionComparison a i).trans
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparison (i ≫ a) v) =
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparison a (i.app (Opposite.op ⦋0⦌) v) := by
  apply Subtype.ext
  funext p
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPre_evaluate p.val.hom a i v

/-- 概要：既存の制限の辺と評価の辺の合成は像の頂点での評価の辺を表す。
方針：豊穣比較の合成を保つ実際の合成三角形へ厳密な可換式を入れる。
規約：点ごとの等式から大域的な等式を推測しない。
使われ方：三角形上の切断による transport の比較。 -/
lemma relativeFunctorPrecompositionComparisonEdge_evaluate {A D B : SSet.{u}}
    (a : A ⟶ B) (i : D ⟶ A) (v : D _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPrecompositionComparisonEdge a i) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (i ≫ a) v) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge a (i.app (Opposite.op ⦋0⦌) v)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedComparisonEdge_hom_trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPrecompositionComparison a i)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparison (i ≫ a) v)
  rw [relativeFunctorPrecompositionComparison_trans_evaluate] at h
  exact h

/-- 概要：任意の図式の二頂点の評価は、その間の辺の transport と可換。
方針：辺への切断制限を挿入し、全対象の始点評価の同型を相殺する。
規約：図式の定義域は任意の単体集合。
使われ方：底の三角形の三辺を共通の切断空間上で比較する。 -/
lemma leftFibrationNaturalTransportEdge_evaluate {A B : SSet.{u}}
    (a : A ⟶ B) (i : (Δ[1] : SSet.{u}) ⟶ A) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge a
          (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (i ≫ a)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge a
          (i.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
  have h₀ := relativeFunctorPrecompositionComparisonEdge_evaluate a i
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have h₁ := relativeFunctorPrecompositionComparisonEdge_evaluate a i
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have hu : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (i ≫ a)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportSourceIso (i ≫ a)).hom := rfl
  rw [hu] at h₀
  calc
    _ = (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPrecompositionComparisonEdge a i) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportSourceIso (i ≫ a)).hom) ≫
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (i ≫ a)) :=
      congrArg (fun f ↦ f ≫ SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (i ≫ a))) h₀.symm
    _ = _ := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge_source]; exact h₁

/-- 概要：底の三角形の長辺の transport は二辺の transport の合成を表す。
方針：三角形上の切断の始点評価で前合成し大域的な始点同型を消去する。
規約：底自体の quasicategory 性は不要。
使われ方：共同評価の二単体の三辺を既存の transport で固定する。 -/
lemma leftFibrationNaturalTransportEdge_hom_comp {B : SSet.{u}}
    (a : (Δ[2] : SSet.{u}) ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (2 : Fin 3) ≫ a)) ≫
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (0 : Fin 3) ≫ a)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (1 : Fin 3) ≫ a)) := by
  let e (i : Fin 3) := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge a (stdSimplex.obj₀Equiv.symm i))
  let t (i : Fin 3) := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ i ≫ a))
  have h₀₁ := leftFibrationNaturalTransportEdge_evaluate a (stdSimplex.δ (2 : Fin 3))
  have h₁₂ := leftFibrationNaturalTransportEdge_evaluate a (stdSimplex.δ (0 : Fin 3))
  have h₀₂ := leftFibrationNaturalTransportEdge_evaluate a (stdSimplex.δ (1 : Fin 3))
  change e 0 ≫ t 2 = e 1 at h₀₁
  change e 1 ≫ t 0 = e 2 at h₁₂
  change e 0 ≫ t 1 = e 2 at h₀₂
  let h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 2)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 2)
  apply (cancel_epi h.hom).1
  change e 0 ≫ (t 2 ≫ t 0) = e 0 ≫ t 1
  rw [← Category.assoc, h₀₁, h₁₂, h₀₂]

/-- 概要：既存の三つの transport の辺を面とする実際の合成三角形。
方針：関手空間の合成の等式を同じ三辺の二単体で実現する。
規約：三辺を同型な別の代表へ変えない。
使われ方：全対象の共同評価を底の二単体へ延長する。 -/
def leftFibrationNaturalTransportCompStruct {B : SSet.{u}}
    (a : (Δ[2] : SSet.{u}) ⟶ B) :
    SSet.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (2 : Fin 3) ≫ a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (0 : Fin 3) ≫ a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.δ (1 : Fin 3) ≫ a)) :=
  SSet.Edge.CompStruct.ofTruncated (Classical.choice
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac (leftFibrationNaturalTransportEdge_hom_comp a)))

/-- 概要：底の退化辺に沿う全対象の transport は恒等射を表す。
方針：一点上の切断評価の大域的同型で前合成して、辺の評価の可換式を使う。
規約：構成済みの transport の辺の類についての等式。
使われ方：共同評価の単体的作用の単位則。 -/
lemma leftFibrationNaturalTransportEdge_hom_id {B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (stdSimplex.σ (0 : Fin 1) ≫ a)) = 𝟙 _ := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 0)
  apply (cancel_epi h.hom).1
  calc
    _ = h.hom := leftFibrationNaturalTransportEdge_evaluate a (stdSimplex.σ (0 : Fin 1))
    _ = _ := (Category.comp_id h.hom).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
