module

public import SerrePositivity.KST.Spectra.D3BiParameterSquare

/-!
概要：二つの実パラメータ四角形の全二次元面を、同じ元の制限図式として回収する。
方針：四角形一方の固定を順序円柱の再添字と照合し、同じ全 Hom 共同評価へ代入する。
規約：角だけでなく各面の全単体で厳密に一致する。単位三角形の可換性は未証明。
使われ方：実二方向図式を、元の一方向図式と比較するための指定面の保持。
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
local instance d3BiFacesSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3BiFacesProductCategory :
    SmallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Preorder.smallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

/-- 第二の四角形を指定角に固定する、元の実面包含。 -/
def d3BiParameterLeftFace (k l : Fin 2) :
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) :=
  lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))

/-- 第一の四角形を指定角に固定する、元の実面包含。 -/
def d3BiParameterRightFace (i j : Fin 2) :
    ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⟶
      (((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) ⊗ (Δ[1] ⊗ Δ[1])) :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) (𝟙 _)

def d3BiParameterLeftOrder (k l : Fin 2) :
    (Fin 2 × Fin 2) →o (Fin 2 × Fin 2) × (Fin 2 × Fin 2) where
  toFun p := (p, (k, l))
  monotone' _ _ h := ⟨h, le_rfl⟩

def d3BiParameterRightOrder (i j : Fin 2) :
    (Fin 2 × Fin 2) →o (Fin 2 × Fin 2) × (Fin 2 × Fin 2) where
  toFun p := ((i, j), p)
  monotone' _ _ h := ⟨le_rfl, h⟩

/-- 面に沿う pairing は、同じ全 Hom を保つ順序円柱の制限に厳密一致。 -/
lemma d3PointedKanBiSquarePair_left (k l : Fin 2) :
    PointedKanInfinity.{u} ◁ d3BiParameterLeftFace k l ≫ d3PointedKanBiSquarePair =
    d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (reindex (C := PointedKanObject.{u}) (d3BiParameterLeftOrder k l)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, t⟩
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

/-- 他方の全二次元面でも、同じ順序円柱の制限と全 Hom を厳密回収する。 -/
lemma d3PointedKanBiSquarePair_right (i j : Fin 2) :
    PointedKanInfinity.{u} ◁ d3BiParameterRightFace i j ≫ d3PointedKanBiSquarePair =
    d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (reindex (C := PointedKanObject.{u}) (d3BiParameterRightOrder i j)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, t⟩
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

/-- 第一方向の全二次元面は、同じテンソルパラメータの制限図式の全族。 -/
lemma d3PointedKanBiParameterSquare_left (k l : Fin 2) :
    d3PointedKanBiParameterSquare D E ≫
      (pre (d3BiParameterLeftFace k l)).app PointedKanInfinity =
    d3PointedKanParameterSquare
      ((d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3TensorParameter D E) := by
  apply uncurry_injective
  rw [uncurry_pre_app, d3PointedKanBiParameterSquare, uncurry_curry,
    d3PointedKanParameterSquare, uncurry_curry]
  rw [← Category.assoc (d3BiParameterLeftFace k l ▷ PointedKanInfinity),
    BraidedCategory.braiding_naturality_left, Category.assoc,
    ← Category.assoc (PointedKanInfinity ◁ d3BiParameterLeftFace k l),
    d3PointedKanBiSquarePair_left]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  simp only [d3TensorParameterDiagram, d3PointedKanParameterDiagram_reindex]

/-- 第二方向の全二次元面も、同じテンソルパラメータの制限図式の全族。 -/
lemma d3PointedKanBiParameterSquare_right (i j : Fin 2) :
    d3PointedKanBiParameterSquare D E ≫
      (pre (d3BiParameterRightFace i j)).app PointedKanInfinity =
    d3PointedKanParameterSquare
      ((d3BiParameterRightOrder i j).toFunctor.op ⋙ d3TensorParameter D E) := by
  apply uncurry_injective
  rw [uncurry_pre_app, d3PointedKanBiParameterSquare, uncurry_curry,
    d3PointedKanParameterSquare, uncurry_curry]
  rw [← Category.assoc (d3BiParameterRightFace i j ▷ PointedKanInfinity),
    BraidedCategory.braiding_naturality_left, Category.assoc,
    ← Category.assoc (PointedKanInfinity ◁ d3BiParameterRightFace i j),
    d3PointedKanBiSquarePair_right]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  simp only [d3TensorParameterDiagram, d3PointedKanParameterDiagram_reindex]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
