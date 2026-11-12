module

public import SerrePositivity.KST.Spectra.SpectrumZeroEvaluationTriangle
public import SerrePositivity.KST.Spectra.CoherentSimplexTraces

/-!
概要：参照零三角形の Hom 経路は元の自然変換の恒等射への作用を定値にしたもの。
方針：元の三段円柱の頂点 fiber を計算し、Hom が単位を経由することを示す。
規約：零三角形の選択を変えない。使われ方：円評価の Hom 正方形の参照辺の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
open CoherentPathCoordinates
local instance zeroTriangleTraceSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の整合入力の頂点で評価した、元の参照零三角形の同じ二単体。 -/
def zeroEvaluationTriangleAt (A : PointedSimplicialSet.{u}) (X : Object A) : Sp.{u} _⦋2⦌ :=
  SSet.yonedaEquiv
    (lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) (𝟙 _) ≫ zeroEvaluationTriangleFamily A)

/-- 参照面の Hom 経路は、元の恒等 Hom を単位から作用させる定値な族。 -/
lemma zeroEvaluationTriangleTrace_factor (A : PointedSimplicialSet.{u}) (X : Object A) :
    triangleTrace (zeroEvaluationTriangleAt A X) =
      toUnit (Δ[1] : SSet.{u}) ≫ eId SSet X ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom (parameterEvaluation A A.hom) X X := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 参照零三角形の Hom 経路は、元の Hom のある零単体での定値経路。 -/
lemma zeroEvaluationTriangleTrace_constant (A : PointedSimplicialSet.{u}) (X : Object A) :
    ∃ y, triangleTrace (zeroEvaluationTriangleAt A X) = SSet.const y := by
  rw [zeroEvaluationTriangleTrace_factor]
  have hu : toUnit (Δ[1] : SSet.{u}) = SSet.const (Y := 𝟙_ SSet.{u}) PUnit.unit := rfl
  rw [hu, SSet.const_comp]
  exact ⟨_, rfl⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
