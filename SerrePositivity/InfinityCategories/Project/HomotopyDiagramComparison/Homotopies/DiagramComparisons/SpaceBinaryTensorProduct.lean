module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpaceProducts
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanNativeConeLeg

/-!
概要：Kan 複体の元の二項直積と二射影を、空間の ∞ 圏の native な積錐にする。
方針：二点の離散図式に対する台の極限性を全豊穣 Hom の極限性へ移す。
規約：頂点は元の直積、脚は fst と snd。使われ方：sifted な全空間積比較の頂点輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の二つの Kan 対象を、宇宙を揃えた二点の離散図式にする。 -/
def kanBinaryDiagram (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : Discrete (ULift.{u} Bool) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  Discrete.functor fun j ↦ if j.down then K else L

/-- 元の直積を頂点、元の二射影を脚とする Kan 対象の錐。 -/
def kanBinaryTensorCone (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : Cone (kanBinaryDiagram K L) where
  pt := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L
  π := Discrete.natTrans fun j ↦ by
    rcases j with ⟨⟨b⟩⟩
    cases b
    · exact snd K.obj L.obj
    · exact fst K.obj L.obj

/-- 元の二射影の錐は台の単体集合で実際に極限。 -/
def kanBinaryTensorCone_forget_isLimit (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (kanBinaryTensorCone K L)) where
  lift s := lift (s.π.app ⟨⟨true⟩⟩) (s.π.app ⟨⟨false⟩⟩)
  fac s j := by
    rcases j with ⟨⟨b⟩⟩
    cases b
    · exact lift_snd _ _
    · exact lift_fst _ _
  uniq s m hm := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hm ⟨⟨true⟩⟩
    · exact hm ⟨⟨false⟩⟩

/-- 元の二項直積と二射影の、coherent な空間値図式上の錐。 -/
def spaceBinaryTensorProductCone (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (kanBinaryDiagram K L)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (kanBinaryTensorCone K L)).cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram _)

/-- 元の二項直積の錐は、空間の ∞ 圏の native な積錐。 -/
lemma spaceBinaryTensorProductCone_isLimit (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spaceBinaryTensorProductCone K L) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_discrete_homLimit (kanBinaryTensorCone K L)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (kanBinaryTensorCone_forget_isLimit K L))

/-- 元の積錐の頂点は、元の Kan 直積の指定頂点に厳密に一致。 -/
lemma spaceBinaryTensorProductCone_vertex (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceBinaryTensorProductCone K L).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L) := by
  rw [spaceBinaryTensorProductCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex]
  rfl

/-- 元の二項直積の native な脚は、元の通常の射影の辺そのもの。 -/
lemma spaceBinaryTensorProductCone_leg_edge (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : Discrete (ULift.{u} Bool)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (spaceBinaryTensorProductCone K L)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kanBinaryTensorCone K L).π.app i)).edge :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (kanBinaryTensorCone K L) i

/-- 元の native な積の脚を Kan 射へ戻すと、元の通常の射影そのもの。 -/
lemma spaceBinaryTensorProductCone_kanLeg (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : Discrete (ULift.{u} Bool)) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (spaceBinaryTensorProductCone K L) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L)
      (spaceBinaryTensorProductCone_vertex K L) i = (kanBinaryTensorCone K L).π.app i := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLegEdge (spaceBinaryTensorProductCone K L)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L) (spaceBinaryTensorProductCone_vertex K L) i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kanBinaryTensorCone K L).π.app i) := by
    apply SSet.Edge.ext
    exact spaceBinaryTensorProductCone_leg_edge K L i
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom h).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom_edge _)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
