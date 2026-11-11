module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.KST.Spectra.D3StageLoopDiagramFamily

/-!
概要：元の四角パラメータ図式と全点つき Kan 入力の共同評価を、一つの全四角形族にする。
方針：元の二つの区間単体を順序円柱に組み、実豊穣関手を全単体で評価する。
規約：四角の全関手は同じ元の内部 Hom 作用。対象別の四角形から自然性は推測しない。
使われ方：d3b② の点つき endpoint loop 図式族の全 Hom 構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
open EnrichedOrderedCylinder
local instance d3SquareOrderCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3ParameterSquareSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 同じ二つの区間単体が指定する四角上の順序写像。 -/
def d3ParameterSquareOrder {n : ℕ} (t : ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) _⦋n⦌) :
    Fin (n + 1) →o Fin 2 × Fin 2 where
  toFun i := (stdSimplex.asOrderHom t.1 i, stdSimplex.asOrderHom t.2 i)
  monotone' _ _ h := ⟨(stdSimplex.asOrderHom t.1).monotone h,
    (stdSimplex.asOrderHom t.2).monotone h⟩

/-- 全点つき Kan 入力と四角パラメータの、同じ全単体の順序円柱への pairing。 -/
def d3PointedKanSquarePair :
    PointedKanInfinity.{u} ⊗ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2 × Fin 2) PointedKanObject.{u}) where
  app _ := ↾fun ⟨F, t⟩ ↦ simplexPair (d3ParameterSquareOrder t) F
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨F, t⟩
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    apply SSet.hom_ext
    intro d'
    apply ConcreteCategory.hom_ext
    intro P
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl

/-- 指定された四角の角への制限は、元の同じ段への包含。 -/
lemma d3PointedKanSquarePair_corner (i j : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) ≫
        d3PointedKanSquarePair =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) (i, j)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

variable (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 元のパラメータ図式と全点つき Kan 入力を評価した、全実四角形族。 -/
def d3PointedKanParameterSquare :
    PointedKanInfinity.{u} ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity :=
  curry ((β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom ≫
    d3PointedKanSquarePair ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D))

/-- 四角の各角は、同じ元のパラメータの内部 Hom ∞ 作用に厳密一致する。 -/
lemma d3PointedKanParameterSquare_corner (i j : Fin 2) :
    d3PointedKanParameterSquare D ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (D.obj (Opposite.op (i, j)))) := by
  rw [d3PointedKanParameterSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hb : lift (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
        (𝟙 PointedKanInfinity.{u}) ≫
      (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom =
        lift (𝟙 PointedKanInfinity.{u})
          (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    rfl
  rw [← Category.assoc, ← Category.assoc, hb, Category.assoc,
    ← Category.assoc, d3PointedKanSquarePair_corner,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3PointedKanParameterDiagram_stage]

/-- 元の共通右射影の段比較を、同じ実段図式終点の endpoint 円模型へ移す。
新しい成分や円交換因子を選ばず、元のパラメータ表示同型を前合成する。 -/
def commonChosenStageEndpointCircleIso (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3StageKanEnriched n))
      ((commonChosenStageLoopDiagramFamily.{u} n ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom endpointCircle)) :=
  commonChosenStageEndpointLoopIso n ≪≫
    (d3PointedKanEndpointLoopIso.precomp
      (commonChosenStageLoopDiagramFamily n ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
