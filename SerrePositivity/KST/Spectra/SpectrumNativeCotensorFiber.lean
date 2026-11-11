module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationFiber
public import SerrePositivity.KST.Spectra.SpectrumNativeCotensorEvaluation

/-!
概要：元の Sp の任意の頂点で、cotensor の入力と普遍評価の実際の BF 模型を同定する。
方針：源射影の逆の零単体から対象を抽出し、coherent nerve の頂点の復元を使う。
規約：入力の逆同値の選択をそのまま保持。使われ方：評価四角形の点ごとの極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCotensorFiberSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- native cotensor の逆射が元の Sp の頂点に割り当てる、実際の整合写像の対象。 -/
def nativeCotensorInput (A : PointedSimplicialSet.{u}) (z : Sp.{u} _⦋0⦌) :
    CotensorCompatible.Object A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((CotensorCompatible.sourceInfinityEquivalence A).inv.app
    (Opposite.op ⦋0⦌) z)

/-- 逆射の像の零単体は、抽出した元の対象の標準頂点そのもの。 -/
lemma nativeCotensorInput_vertex (A : PointedSimplicialSet.{u}) (z : Sp.{u} _⦋0⦌) :
    (CotensorCompatible.sourceInfinityEquivalence A).inv.app (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (nativeCotensorInput A z) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm

/-- native cotensor の頂点での値は、逆射が選んだ入力の実際の BF cotensor。 -/
lemma nativeCotensor_fiber_vertex (A : PointedSimplicialSet.{u}) (z : Sp.{u} _⦋0⦌) :
    (nativeCotensor A).app (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (cotensor A (nativeCotensorInput A z).val) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (CotensorCompatible.cotensorEnriched A)).app _
    ((CotensorCompatible.sourceInfinityEquivalence A).inv.app _ z) = _
  rw [nativeCotensorInput_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  rfl

/-- 元の Sp の頂点での評価の族は、選ばれた入力の元の豊穣評価の nerve に厳密一致。 -/
lemma nativeCotensorEvaluationFamily_fiber (A : PointedSimplicialSet.{u})
    (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const z)
        (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}))) ≫ nativeCotensorEvaluationFamily A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (CotensorCompatible.evaluationFiberEnriched A (nativeCotensorInput A z)) := by
  rw [nativeCotensorEvaluationFamily, ← Category.assoc, lift_map,
    SSet.const_comp, Category.id_comp, nativeCotensorInput_vertex,
    CotensorCompatible.evaluationNerveFamily_fiber]

/-- 頂点での評価の終点は、元の逆射が選んだ BF 入力の標準頂点。 -/
lemma nativeCotensorEvaluationFamily_target_vertex (A : PointedSimplicialSet.{u})
    (z : Sp.{u} _⦋0⦌) :
    ((CotensorCompatible.sourceInfinityEquivalence A).inv ≫
      CotensorCompatible.sourceInfinityMap A).app (Opposite.op ⦋0⦌) z =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (nativeCotensorInput A z).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (CotensorCompatible.sourceEnriched A)).app _
    ((CotensorCompatible.sourceInfinityEquivalence A).inv.app _ z) = _
  rw [nativeCotensorInput_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
