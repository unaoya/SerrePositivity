module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderEdge
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：パラメータ辺を通常の射の coherent な辺と同定し、両端を固定する。
方針：標準一単体から射データを抽出し、その一意な復元を使う。
規約：局所 Kan 性を仮定しない。使われ方：円の生成辺の三角形の境界の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {A : SSet.{u}} (i : 𝟙_ SSet.{u} ⟶ A)

/-- 二対象の円柱の、指定した単位パラメータによる通常の射。 -/
def parameterHom :
    (⟨false, ⟨PUnit.unit⟩⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) ⟶ ⟨true, ⟨PUnit.unit⟩⟩ :=
  ForgetEnrichment.homOf SSet (lift i (𝟙 _))

/-- パラメータ辺の標準一単体から取り出す射は、元のパラメータ射そのもの。 -/
lemma parameterEdge_arrowData :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (SSet.yonedaEquiv (parameterEdge.{u, v} i)) =
      ⟨⟨false, ⟨PUnit.unit⟩⟩, ⟨true, ⟨PUnit.unit⟩⟩, parameterHom i⟩ := by
  change (⟨_, _, (SimplicialCategory.homEquiv' _ _).symm _⟩ :
    Σ X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}, X ⟶ Y) = _
  congr 2
  apply (SimplicialCategory.homEquiv' _ _).injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- パラメータ辺は、通常のパラメータ射から作る coherent な辺に厳密一致。 -/
lemma parameterEdge_eq :
    parameterEdge.{u, v} i = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (parameterHom i)).edge := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v})).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData _
  rw [parameterEdge_arrowData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]

/-- パラメータ辺の始点は二対象の円柱の左端。 -/
lemma parameterEdge_source :
    stdSimplex.δ (1 : Fin 2) ≫ parameterEdge.{u, v} i = SSet.const (leftVertex A) := by
  rw [parameterEdge_eq, SSet.Edge.δ_one_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero]
  rfl

/-- パラメータ辺の終点は二対象の円柱の右端。 -/
lemma parameterEdge_target :
    stdSimplex.δ (0 : Fin 2) ≫ parameterEdge.{u, v} i = SSet.const (rightVertex A) := by
  rw [parameterEdge_eq, SSet.Edge.δ_zero_yonedaEquiv_symm, SSet.yonedaEquiv_symm_zero]
  rfl

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
