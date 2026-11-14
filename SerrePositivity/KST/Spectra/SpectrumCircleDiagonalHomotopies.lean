module

public import SerrePositivity.KST.Spectra.SpectrumCircleHomSquareBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.IntervalSquareHomotopies
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SquareConstantCorners

/-!
概要：元の生成 loop と companion の Hom 経路を、同じ対角へ両端固定で動かす。
方針：元の Hom 正方形へ最小値の二つの変形を合成し、四隅と定値辺を零頂点へ同定する。
規約：元の三単体と普遍評価を保持。使われ方：元の円評価錐と BK 錐の切断点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の円 cotensor と入力の Hom の、零射に基づく点つき空間。 -/
def circleEvaluationPointedHom (z : Sp.{u} _⦋0⦌) : PointedSimplicialSet.{u} :=
  RawSpectrumMapping.pointedSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence

/-- 元の Hom 正方形の四隅は、全て元の零 Hom 頂点。 -/
lemma circleEvaluationHomSquare_corner (z : Sp.{u} _⦋0⦌) (i j : Fin 2) :
    (circleEvaluationHomSquare z).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
        (circleEvaluationPointedHom z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.corners_of_bottom_loop
    (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (circleEvaluationHomSquare z) (circleEvaluationHomSquare_skipSecond z)
    (circleEvaluationHomSquare_includeFirst_constant z)
    (circleEvaluationHomSquare_includeSecond_constant z) i j

/-- 元の右辺の定値は、元の零 Hom 頂点での定値写像そのもの。 -/
lemma circleEvaluationHomSquare_right_zero (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        circleEvaluationHomSquare z = SSet.const (circleEvaluationPointedHom z).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_of_vertex (circleEvaluationHomSquare_includeFirst_constant z)
  change (circleEvaluationHomSquare z).app _
    ((SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 1)).app _
      (stdSimplex.obj₀Equiv.symm 0), stdSimplex.obj₀Equiv.symm 0) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex]
  exact circleEvaluationHomSquare_corner z 1 0

/-- 元の上辺も、同じ零 Hom 頂点での定値写像そのもの。 -/
lemma circleEvaluationHomSquare_top_zero (z : Sp.{u} _⦋0⦌) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        circleEvaluationHomSquare z = SSet.const (circleEvaluationPointedHom z).basepoint := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.constant_of_vertex (circleEvaluationHomSquare_includeSecond_constant z)
  change (circleEvaluationHomSquare z).app _ (stdSimplex.obj₀Equiv.symm 0,
    (SSet.const (X := (Δ[1] : SSet.{u})) (stdSimplex.obj₀Equiv.symm 1)).app _
      (stdSimplex.obj₀Equiv.symm 0)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.const_vertex]
  exact circleEvaluationHomSquare_corner z 0 1

/-- 元の Hom 正方形の対角経路。 -/
def circleEvaluationHomDiagonal (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⟶ (circleEvaluationPointedHom z).right :=
  lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 _) ≫ circleEvaluationHomSquare z

/-- 元の生成 loop の経路から、同じ正方形の対角への実際のホモトピー。 -/
def circleEvaluationLoopDiagonalHomotopy (z : Sp.{u} _⦋0⦌) :
    SSet.Homotopy
      (SSet.yonedaEquiv.symm
        (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val).edge)
      (circleEvaluationHomDiagonal z) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy (circleEvaluationHomSquare z)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy (circleEvaluationHomSquare z)).h₀,
      circleEvaluationHomSquare_skipSecond]
    rfl
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy (circleEvaluationHomSquare z)).h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact False.elim a.property

/-- 元の companion 経路から、同じ対角への実際のホモトピー。 -/
def circleEvaluationCompanionDiagonalHomotopy (z : Sp.{u} _⦋0⦌) :
    SSet.Homotopy (circleEvaluationCompanionHomPath z) (circleEvaluationHomDiagonal z) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy (circleEvaluationHomSquare z)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy (circleEvaluationHomSquare z)).h₀,
      circleEvaluationHomSquare_skipFirst]
    rfl
  h₁ := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy (circleEvaluationHomSquare z)).h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact False.elim a.property

/-- 生成 loop の対角へのホモトピーは、始点の零 Hom 頂点を固定する。 -/
lemma circleEvaluationLoopDiagonalHomotopy_source (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (circleEvaluationLoopDiagonalHomotopy z).h =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy (circleEvaluationHomSquare z)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy_source, circleEvaluationHomSquare_corner]

/-- 生成 loop の対角へのホモトピーは、終点の同じ零 Hom 頂点も固定する。 -/
lemma circleEvaluationLoopDiagonalHomotopy_target (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (circleEvaluationLoopDiagonalHomotopy z).h =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy (circleEvaluationHomSquare z)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomHomotopy_target, circleEvaluationHomSquare_right_zero]

/-- companion の対角へのホモトピーも、始点の零 Hom 頂点を固定する。 -/
lemma circleEvaluationCompanionDiagonalHomotopy_source (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (circleEvaluationCompanionDiagonalHomotopy z).h =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy (circleEvaluationHomSquare z)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy_source, circleEvaluationHomSquare_corner]

/-- companion の対角へのホモトピーも、終点の同じ零 Hom 頂点を固定する。 -/
lemma circleEvaluationCompanionDiagonalHomotopy_target (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (circleEvaluationCompanionDiagonalHomotopy z).h =
      SSet.const (circleEvaluationPointedHom z).basepoint := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy (circleEvaluationHomSquare z)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftHomotopy_target, circleEvaluationHomSquare_top_zero]

end SerrePositivity.KST.Spectra.OmegaSpectrum
