module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredFixedBasePullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers

/-!
概要：固定底上の strict filtered 余極限の fiber は、元の各 fiber の余極限。
方針：元の fiber の pullback 正方形に filtered 余極限の有限極限保存を適用する。
規約：比較同型は同じ全空間への射を保つ。頂点だけの同値で代用しない。
使われ方：strict right fibration 模型から coherent な前層余錐への比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 元の底の同じ頂点での fiber 図式。 -/
def rightFibrationFiberDiagram (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    I ⥤ SSet.{u} where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (F.obj i).val.hom b
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (F.map f).left (Over.w (F.map f)) b
  map_id i := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _ b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.id_comp]
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F).map (𝟙 i) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _ b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, Category.assoc]
    exact congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ b ≫ t)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F).map_comp f g)

/-- 同じ fiber 図式から元の全空間図式への包含。 -/
def rightFibrationFiberInclusion (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    rightFibrationFiberDiagram F b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (F.obj i).val.hom b
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ (F.map f).left (Over.w (F.map f)) b

/-- 同じ fiber 図式の固定された零単体への射。 -/
def rightFibrationFiberTerminal (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    rightFibrationFiberDiagram F b ⟶ (Functor.const I).obj (Δ[0] : SSet.{u}) where
  app _ := stdSimplex.isTerminalObj₀.from _
  naturality _ _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _

/-- strict 余極限の元の fiber 正方形は実際の pullback。 -/
lemma strictRightFibrationColimitFiber_isPullback [IsFiltered I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    IsPullback (colim.map (rightFibrationFiberInclusion F b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fixedBaseColimitMap (rightFibrationFiberTerminal F b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) (SSet.const b : Δ[0] ⟶ B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.filteredFixedBaseColimit_isPullback _ _ _ _ (fun i =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback (F.obj i).val.hom b)

/-- 元の fiber 図式の余極限と、同じ strict 余極限の fiber の比較同型。 -/
def strictRightFibrationColimitFiberIso [IsFiltered I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    colimit (rightFibrationFiberDiagram F b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) b :=
  (strictRightFibrationColimitFiber_isPullback F b).isoPullback ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) b).isoPullback.symm

@[reassoc (attr := simp)]
lemma strictRightFibrationColimitFiberIso_hom_ι [IsFiltered I]
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    (strictRightFibrationColimitFiberIso F b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightFibrationColimitProjection F) b =
        colim.map (rightFibrationFiberInclusion F b) := by
  dsimp only [strictRightFibrationColimitFiberIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
