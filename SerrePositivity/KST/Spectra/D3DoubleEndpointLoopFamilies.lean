module

public import SerrePositivity.KST.Spectra.D3TensorEndpointZeros

/-!
概要：実二方向端点図式の二つの四角形方向を、同じ全単体の実 loop 図式族へ因子化する。
方針：構成した各面の実極限性と、point・based path テンソルの実零角を同時に保持する。
規約：入力 Hom の作用や各面を選び直さない。既存模型の単位比較は未証明。
使われ方：二方向の loop 表示を、終点固定の全図式普遍性で比較するための実入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3DoubleLoopSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3DoubleLoopProductCategory :
    SmallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Preorder.smallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

/-- 任意の元のパラメータ四角形の角は、同じ入力に対する元の内部 Hom 頂点。 -/
lemma d3ParameterSquare_corner_vertex
    (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u})
    (Y : PointedKanObject.{u}) (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
      ((d3PointedKanParameterSquare D).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))) i j =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((d3PointedKanIhom (D.obj (Opposite.op (i, j)))).obj Y) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_vertex_evaluation]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (d3PointedKanParameterSquare_corner D i j) (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ Y)

/-- 第一方向の各実面は、構成済みの同じ両零角と実極限性を持つ loop 図式。 -/
lemma d3DoubleEndpointLeftFace_isLoop (k l : Fin 2) (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
      ((d3DoubleEndpointSquare ≫ (pre (d3BiParameterLeftFace k l)).app
        PointedKanInfinity).app _ v) := by
  obtain ⟨Y, hY⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv PointedKanObject.{u}).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y = v at hY
  rw [← hY, d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [d3ParameterSquare_corner_vertex]
    exact d3PointedKanPointTensor_isZero (d3EndpointParameterObj (k, l)) Y
  · rw [d3ParameterSquare_corner_vertex]
    exact d3PointedKanPathTensor_isZero (d3EndpointParameterObj (k, l)) Y
  · simpa only [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_left] using
      (d3DoubleEndpointSquare_left_isPullback k l Y)

/-- 第二方向でも、同じ実面が両零角と実極限性を持つ loop 図式。 -/
lemma d3DoubleEndpointRightFace_isLoop (i j : Fin 2) (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
      ((d3DoubleEndpointSquare ≫ (pre (d3BiParameterRightFace i j)).app
        PointedKanInfinity).app _ v) := by
  obtain ⟨Y, hY⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv PointedKanObject.{u}).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y = v at hY
  rw [← hY, d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_right]
  refine ⟨?_, ?_, ?_⟩
  · rw [d3ParameterSquare_corner_vertex]
    exact d3PointedKanTensorPoint_isZero (d3EndpointParameterObj (i, j)) Y
  · rw [d3ParameterSquare_corner_vertex]
    exact d3PointedKanTensorPath_isZero (d3EndpointParameterObj (i, j)) Y
  · simpa only [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_right] using
      (d3DoubleEndpointSquare_right_isPullback i j Y)

/-- 元の四次元図式の第一方向の面を、その全 Hom 作用のまま実 loop 全図式に保持する。 -/
def d3DoubleEndpointLeftLoopFamily (k l : Fin 2) :
    PointedKanInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (A := PointedKanInfinity.{u})
    (X := (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
    (d3DoubleEndpointSquare ≫ (pre (d3BiParameterLeftFace k l)).app PointedKanInfinity)
    (d3DoubleEndpointLeftFace_isLoop k l)

/-- 同じ四次元図式の第二方向の面も、元の全 Hom・全単体を保つ実 loop 族。 -/
def d3DoubleEndpointRightLoopFamily (i j : Fin 2) :
    PointedKanInfinity.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (A := PointedKanInfinity.{u})
    (X := (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj PointedKanInfinity)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
    (d3DoubleEndpointSquare ≫ (pre (d3BiParameterRightFace i j)).app PointedKanInfinity)
    (d3DoubleEndpointRightFace_isLoop i j)

lemma d3DoubleEndpointLeftLoopFamily_ι (k l : Fin 2) :
    d3DoubleEndpointLeftLoopFamily.{u} k l ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    d3DoubleEndpointSquare ≫ (pre (d3BiParameterLeftFace k l)).app PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

lemma d3DoubleEndpointRightLoopFamily_ι (i j : Fin 2) :
    d3DoubleEndpointRightLoopFamily.{u} i j ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    d3DoubleEndpointSquare ≫ (pre (d3BiParameterRightFace i j)).app PointedKanInfinity :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 第一方向の実 loop 族の各角も、元の二つのパラメータの全 Hom 作用を厳密回収。 -/
lemma d3DoubleEndpointLeftLoopFamily_corner (k l i j : Fin 2) :
    d3DoubleEndpointLeftLoopFamily.{u} k l ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
      (d3EndpointParameterObj.{u} (i, j) ⊗ d3EndpointParameterObj.{u} (k, l))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointLeftLoopFamily_ι,
    d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_left,
    d3PointedKanParameterSquare_corner]
  rfl

/-- 第二方向の実 loop 族でも、同じ二つの元パラメータを同じ指定順序で回収する。 -/
lemma d3DoubleEndpointRightLoopFamily_corner (i j k l : Fin 2) :
    d3DoubleEndpointRightLoopFamily.{u} i j ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity k l =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
      (d3EndpointParameterObj.{u} (i, j) ⊗ d3EndpointParameterObj.{u} (k, l))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointRightLoopFamily_ι,
    d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_right,
    d3PointedKanParameterSquare_corner]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
