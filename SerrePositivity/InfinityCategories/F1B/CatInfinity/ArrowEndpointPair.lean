module

public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.F1B.Fibrations.EquivalenceLifting
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ArrowBoundary
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ArrowBoundaryEvaluation

/-!
概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryEvaluationIso (C : SSet.{u}) : ((ihom arrowBoundary).obj C) ≅ C ⊗ C :=
  ⟨arrowBoundaryEvaluation C, arrowBoundaryEvaluationInv C,
    arrowBoundaryEvaluation_hom_inv C, arrowBoundaryEvaluation_inv_hom C⟩
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowEndpointPair (C : SSet.{u}) : ((ihom (Δ[1] : SSet.{u})).obj C) ⟶ C ⊗ C :=
  CartesianMonoidalCategory.lift
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0))
    (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1))
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowEndpointPair_restriction (C : SSet.{u}) :
    arrowEndpointPair C = (pre arrowBoundaryι).app C ≫ (arrowBoundaryEvaluationIso C).hom := by
  rfl
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowEndpointPair_kanEquivalenceLifting (C : SSet.{u}) [Quasicategory C] :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (arrowEndpointPair C) := by
  rw [arrowEndpointPair_restriction]
  intro K L i hi he
  have : HasLiftingProperty i ((pre arrowBoundaryι).app C) :=
    SerrePositivity.InfinityCategories.F1B.equivalenceLifting_pre arrowBoundaryι i hi he
  infer_instance
/-- 概要：矢印圏の両端評価の充填性。
方針：二点への制限と厳密な評価同型で既存の持ち上げ性を輸送する。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
instance arrowEndpointPair_innerFibration (C : SSet.{u}) [Quasicategory C] :
    InnerFibration (arrowEndpointPair C) :=
  SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration (arrowEndpointPair_kanEquivalenceLifting C)

/-- 概要：両端評価の任意の内部 Hom は inner fibration。
方針：単射な前合成同値の右持ち上げ条件の内部 Hom による保存を使う。
規約：試験単体集合 K の quasicategory 性は不要。
使われ方：全試験関手 core の引き戻し表示。 -/
instance arrowEndpointPair_internalHom_innerFibration (C K : SSet.{u}) [Quasicategory C] :
    InnerFibration ((ihom K).map (arrowEndpointPair C)) :=
  SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.innerFibration
    (SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.internalHom (arrowEndpointPair_kanEquivalenceLifting C) K)

end SerrePositivity.InfinityCategories.F2
