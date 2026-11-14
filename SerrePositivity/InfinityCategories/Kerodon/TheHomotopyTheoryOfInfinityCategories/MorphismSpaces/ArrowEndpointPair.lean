module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ArrowBoundaryEvaluation

/-!
概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryEvaluationIso (C : SSet.{u}) : ((ihom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundary).obj C) ≅ C ⊗ C :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation C, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluationInv C,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation_hom_inv C, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryEvaluation_inv_hom C⟩
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowEndpointPair (C : SSet.{u}) : ((ihom (Δ[1] : SSet.{u})).obj C) ⟶ C ⊗ C :=
  CartesianMonoidalCategory.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1))
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowEndpointPair_restriction (C : SSet.{u}) :
    arrowEndpointPair C = (pre _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι).app C ≫ (arrowBoundaryEvaluationIso C).hom := by
  rfl
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowEndpointPair_kanEquivalenceLifting (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (arrowEndpointPair C) := by
  rw [arrowEndpointPair_restriction]
  intro K L i hi he
  have : HasLiftingProperty i ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι).app C) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceLifting_pre _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.arrowBoundaryι i hi he
  infer_instance
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
instance arrowEndpointPair_innerFibration (C : SSet.{u}) [Quasicategory C] :
    InnerFibration (arrowEndpointPair C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration (arrowEndpointPair_kanEquivalenceLifting C)

/-- 概要：両端評価の任意の内部 Hom は inner fibration。
方針：単射な前合成同値の右持ち上げ条件の内部 Hom による保存を使う。
規約：試験単体集合 K の quasicategory 性は不要。
使われ方：全試験関手 core の引き戻し表示。 -/
instance arrowEndpointPair_internalHom_innerFibration (C K : SSet.{u}) [Quasicategory C] :
    InnerFibration ((ihom K).map (arrowEndpointPair C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom (arrowEndpointPair_kanEquivalenceLifting C) K)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.7.11" (partial := component) "仮定：準圏 C（HTT と一致）。結論：同じ arrowEndpointPair:Fun(Δ1,C)→C×C が InnerFibration であり、bifibration の定義の最初の明示条件に一致する。残る二つの条件付き outer-horn filling は含まず、EquivalenceLifting の別条件をその代用にはしない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair_innerFibration
