module

public import SerrePositivity.KST.Spectra.D3ParameterPullbackCriterion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SmashMonomorphisms
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：実二方向端点図式の二つの四角形方向の各面を、同じ実 ∞ pullback として認証する。
方針：元の端点 pushout をテンソルで保存し、元の単射の保存と全 Hom 極限性へ代入する。
規約：零角認証・loop 表示の比較・単位三角形の可換性は、この極限認証と区別する。
使われ方：転置模型の単位照合に用いる、指定二方向図式の内側の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3DoublePullbackSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3DoublePullbackProductCategory :
    SmallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Preorder.smallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

section
variable (D E : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 第一方向の面の同じ実射は、元の制限射の右テンソルそのもの。 -/
lemma d3BiParameterLeft_arrow (k l : Fin 2) {p q : Fin 2 × Fin 2} (h : p ≤ q) :
    d3ParameterArrow ((d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3TensorParameter D E) h =
      d3ParameterArrow D h ▷ E.obj (Opposite.op (k, l)) := by
  change d3ParameterArrow D h ⊗ₘ d3ParameterArrow E (le_rfl : (k, l) ≤ (k, l)) = _
  rw [d3ParameterArrow_id, tensorHom_id]

/-- 第二方向の面の実射も、元の制限射の左テンソルそのもの。 -/
lemma d3BiParameterRight_arrow (i j : Fin 2) {p q : Fin 2 × Fin 2} (h : p ≤ q) :
    d3ParameterArrow ((d3BiParameterRightOrder i j).toFunctor.op ⋙ d3TensorParameter D E) h =
      D.obj (Opposite.op (i, j)) ◁ d3ParameterArrow E h := by
  change d3ParameterArrow D (le_rfl : (i, j) ≤ (i, j)) ⊗ₘ d3ParameterArrow E h = _
  rw [d3ParameterArrow_id, id_tensorHom]

include D E in
/-- 抽象パラメータの段階で、同じ pushout の右テンソル保存を照合する。 -/
lemma d3BiParameterLeft_isPushout (hD : D3ParameterIsPushout D) (k l : Fin 2) :
    D3ParameterIsPushout
      ((d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3TensorParameter D E) := by
  dsimp only [D3ParameterIsPushout]
  rw [d3BiParameterLeft_arrow, d3BiParameterLeft_arrow,
    d3BiParameterLeft_arrow, d3BiParameterLeft_arrow]
  exact hD.map (tensorRight (E.obj (Opposite.op (k, l))))

include D E in
/-- 抽象パラメータの段階で、同じ pushout の左テンソル保存を照合する。 -/
lemma d3BiParameterRight_isPushout (hE : D3ParameterIsPushout E) (i j : Fin 2) :
    D3ParameterIsPushout
      ((d3BiParameterRightOrder i j).toFunctor.op ⋙ d3TensorParameter D E) := by
  dsimp only [D3ParameterIsPushout]
  rw [d3BiParameterRight_arrow, d3BiParameterRight_arrow,
    d3BiParameterRight_arrow, d3BiParameterRight_arrow]
  exact hE.map (tensorLeft (D.obj (Opposite.op (i, j))))
end

/-- 元の端点パラメータ四角形は、構成済みの同じ cofiber pushout。 -/
lemma d3EndpointParameter_isPushout : D3ParameterIsPushout d3EndpointParameter.{u} := by
  exact pointedCofiber_isPushout _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}

/-- 元の端点 pushout を右テンソルで保存した、第一方向の実パラメータ面。 -/
lemma d3DoubleEndpointLeftParameter_isPushout (k l : Fin 2) :
    D3ParameterIsPushout
      ((d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3DoubleEndpointParameter.{u}) := by
  exact d3BiParameterLeft_isPushout d3EndpointParameter d3EndpointParameter
    d3EndpointParameter_isPushout k l

/-- 元の端点 pushout を左テンソルで保存した、第二方向の実パラメータ面。 -/
lemma d3DoubleEndpointRightParameter_isPushout (i j : Fin 2) :
    D3ParameterIsPushout
      ((d3BiParameterRightOrder i j).toFunctor.op ⋙ d3DoubleEndpointParameter.{u}) := by
  exact d3BiParameterRight_isPushout d3EndpointParameter d3EndpointParameter
    d3EndpointParameter_isPushout i j

/-- 第一方向の元の端点射は、任意の第二方向パラメータとのテンソル後も実単射。 -/
lemma d3DoubleEndpointLeftParameter_mono (k l : Fin 2) :
    Mono (d3ParameterArrow
      ((d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3DoubleEndpointParameter.{u})
      (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right := by
  rw [d3DoubleEndpointParameter, d3BiParameterLeft_arrow]
  change Mono (PointedObject.smashMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}
    (𝟙 (d3EndpointParameterObj (k, l)))).right
  infer_instance

/-- 第二方向の元の端点射も、任意の第一方向パラメータとのテンソル後に実単射。 -/
lemma d3DoubleEndpointRightParameter_mono (i j : Fin 2) :
    Mono (d3ParameterArrow
      ((d3BiParameterRightOrder i j).toFunctor.op ⋙ d3DoubleEndpointParameter.{u})
      (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right := by
  rw [d3DoubleEndpointParameter, d3BiParameterRight_arrow]
  change Mono (d3EndpointParameterObj (i, j) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}).right
  infer_instance

/-- 実四次元全図式の第一方向の各面は、同じ元の作用を持つ ∞ pullback。 -/
lemma d3DoubleEndpointSquare_left_isPullback (k l : Fin 2) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
      ((d3DoubleEndpointSquare ≫ (MonoidalClosed.pre (d3BiParameterLeftFace k l)).app
        PointedKanInfinity).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))) := by
  rw [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_left]
  let D := (d3BiParameterLeftOrder k l).toFunctor.op ⋙ d3DoubleEndpointParameter.{u}
  have : Mono (d3ParameterArrow D
      (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right :=
    d3DoubleEndpointLeftParameter_mono k l
  exact d3ParameterSquare_isPullback D (d3DoubleEndpointLeftParameter_isPushout k l) Y

/-- 同じ実四次元図式の第二方向の各面も、元の作用を保つ ∞ pullback。 -/
lemma d3DoubleEndpointSquare_right_isPullback (i j : Fin 2) (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
      ((d3DoubleEndpointSquare ≫ (MonoidalClosed.pre (d3BiParameterRightFace i j)).app
        PointedKanInfinity).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y))) := by
  rw [d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_right]
  let D := (d3BiParameterRightOrder i j).toFunctor.op ⋙ d3DoubleEndpointParameter.{u}
  have : Mono (d3ParameterArrow D
      (show ((1, 0) : Fin 2 × Fin 2) ≤ (1, 1) by decide)).right :=
    d3DoubleEndpointRightParameter_mono i j
  exact d3ParameterSquare_isPullback D (d3DoubleEndpointRightParameter_isPushout i j) Y

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
