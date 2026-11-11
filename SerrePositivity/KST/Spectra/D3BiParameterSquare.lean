module

public import SerrePositivity.KST.Spectra.D3TensorParameterDiagram

/-!
概要：二つの全パラメータ四角形と全 Kan 入力を、実際の四次元単体的図式族にする。
方針：四つの区間座標を同じ順序円柱へ pairing し、実豊穣共同評価を全単体で適用する。
規約：16 個の対象だけでなく全 Hom・全単体作用を保持する。単位三角形は未証明。
使われ方：転置模型の単位比較のため、実端点四角形を二方向同時に追跡する基礎図式。
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
local instance d3BiParameterSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3BiParameterProductCategory :
    SmallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Preorder.smallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

/-- 二つの四角形の四つの座標を、同じ積順序に保つ。 -/
def d3BiParameterSquareOrder {n : ℕ}
    (t : (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) _⦋n⦌) :
    Fin (n + 1) →o (Fin 2 × Fin 2) × (Fin 2 × Fin 2) where
  toFun i := (d3ParameterSquareOrder t.1 i, d3ParameterSquareOrder t.2 i)
  monotone' _ _ h := ⟨(d3ParameterSquareOrder t.1).monotone h,
    (d3ParameterSquareOrder t.2).monotone h⟩

/-- 元の全 Kan 入力と四つの区間を、同じ実順序円柱の nerve へ組み合わせる。 -/
def d3PointedKanBiSquarePair :
    PointedKanInfinity.{u} ⊗ (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) ⟶
      SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) PointedKanObject.{u}) where
  app _ := ↾fun ⟨F, t⟩ ↦ simplexPair (d3BiParameterSquareOrder t) F
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

/-- 16 個の角のいずれでも、元の同じ段包含そのものを回収する。 -/
lemma d3PointedKanBiSquarePair_corner (i j k l : Fin 2) :
    lift (𝟙 PointedKanInfinity.{u})
      (SSet.const ((stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j),
        (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))) ≫
      d3PointedKanBiSquarePair =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) ((i, j), (k, l))) := by
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

variable (D E : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 二つの全四角形と元の全 Kan Hom を同時評価した、実四次元図式族。 -/
def d3PointedKanBiParameterSquare : PointedKanInfinity.{u} ⟶
    (ihom (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1]))).obj PointedKanInfinity :=
  curry ((β_ (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) PointedKanInfinity).hom ≫
    d3PointedKanBiSquarePair ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3TensorParameterDiagram D E))

/-- 各角の全関手は、同じ二つの元パラメータのテンソルからの内部 Hom 作用。 -/
lemma d3PointedKanBiParameterSquare_corner (i j k l : Fin 2) :
    d3PointedKanBiParameterSquare D E ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j),
        (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
      (D.obj (Opposite.op (i, j)) ⊗ E.obj (Opposite.op (k, l)))) := by
  rw [d3PointedKanBiParameterSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hb : lift
      (SSet.const ((stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j),
        (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)))
      (𝟙 PointedKanInfinity.{u}) ≫
      (β_ (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) PointedKanInfinity).hom =
      lift (𝟙 PointedKanInfinity.{u})
        (SSet.const ((stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j),
          (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    rfl
  rw [← Category.assoc, ← Category.assoc, hb, Category.assoc,
    ← Category.assoc, d3PointedKanBiSquarePair_corner, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    d3TensorParameterDiagram_stage]

/-- 元の二つの実端点四角形を、全 Kan Hom 上の同じ四次元図式として保持する。 -/
def d3DoubleEndpointSquare : PointedKanInfinity.{u} ⟶
    (ihom (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1]))).obj PointedKanInfinity :=
  d3PointedKanBiParameterSquare d3EndpointParameter d3EndpointParameter

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
