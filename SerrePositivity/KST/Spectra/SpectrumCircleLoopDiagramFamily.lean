module

public import SerrePositivity.KST.Spectra.SpectrumNativeCircleIsPullback
public import SerrePositivity.KST.Spectra.SpectrumNativeLoopFunctor

/-!
概要：元の円評価四角形の全単体の族を、Sp の実際の loop 図式の族へ持ち上げる。
方針：二変数を交換して curry し、元の各四角形の零角と引き戻し性を使う。
規約：元の四角形の族を保持。使われ方：native loop と円 cotensor の関手同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の四角形の全族を、Sp から四角形の関手単体集合への射に転置する。 -/
def circleSquareDiagramFamily : Sp.{u} ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u + 1})).obj Sp.{u} :=
  curry ((β_ (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) Sp.{u}).hom ≫ nativeCircleEvaluationSquareFamily)

/-- 転置した族の頂点は、同じ元の四角形の関手頂点。 -/
lemma circleSquareDiagramFamily_vertex (z : Sp.{u} _⦋0⦌) :
    circleSquareDiagramFamily.app (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nativeCircleEvaluationSquare z) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  dsimp [circleSquareDiagramFamily, curry]
  rfl

/-- 全頂点で、元の二つの零角と元の引き戻し性を保持する。 -/
lemma circleSquareDiagramFamily_isLoop (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (circleSquareDiagramFamily.app (Opposite.op ⦋0⦌) z) := by
  rw [circleSquareDiagramFamily_vertex]
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
    (nativeCircleEvaluationSquare z))) 0 1) ∧ _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex]
  exact ⟨nativeCircleEvaluationSquare_zeroCorner_isZero z 0,
    nativeCircleEvaluationSquare_zeroCorner_isZero z 1,
    nativeCircleEvaluationSquare_isPullback z⟩

/-- 元の全四角形族からなる実際の loop 図式の族。 -/
def circleLoopDiagramFamily : Sp.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex circleSquareDiagramFamily circleSquareDiagramFamily_isLoop

/-- loop 図式の包含は、元の同じ全四角形族を厳密に回収する。 -/
lemma circleLoopDiagramFamily_ι :
    circleLoopDiagramFamily.{u} ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
      circleSquareDiagramFamily := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- loop 図式族の任意の角の評価は、元の四角形族の同じ角への制限。 -/
lemma circleLoopDiagramFamily_evaluation (i j : Fin 2) :
    circleLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} i j =
      lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) ≫
        nativeCircleEvaluationSquareFamily := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation, ← Category.assoc, circleLoopDiagramFamily_ι,
    circleSquareDiagramFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, ← Category.assoc]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
