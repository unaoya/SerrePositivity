module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality

/-!
概要：G8 の正本の比較の後段を、元の選択のまま独立に表示する。
方針：切断錐から指定極限への辺、宇宙変更、表現可能値の比較を同じ順で合成する。
規約：既存の比較の本文・型・選択を変更しない。
使われ方：G8 の四角形②の全族自然性の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：元の小さい切断対象を、同じ図式の指定極限の値へ送る同じ比較。
方針：切断錐と指定極限錐の標準頂点同型を値で読む。
規約：正本の比較と同じ辺の代表と逆の選択を保持する。
使われ方：G8 の後段の因子。 -/
def sectionsLimitValueEquivalence {B : SSet.{u}}
    (g : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCone g) (hc : IsLimitCone c) :
    QCatEquivalence (coherentSpaceSectionsObject g).obj (spaceInfinityObject c.vertex).obj := by
  let e := limitVertexIso (coherentDiagramSectionsCone g) c
    (coherentDiagramSectionsCone_isLimit g) hc
  have ev : VertexIso (coherentSpaceSectionsVertex g) c.vertex := by
    rw [← coherentDiagramSectionsCone_vertex g]
    exact e
  letI : KanComplex (simplicialSections (smallLeftUnstraighteningProjection g)) :=
    (coherentSpaceSectionsObject g).isKanComplex
  exact (qCatEquivalenceOfIso (eqToIso (coherentSpaceSectionsVertex_object g))).symm.trans
    (SetWeight.spaceValueEquivalence ev)

variable {I : Type u} [SmallCategory I] (P : I ⥤ Type u)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c : JoinCone (SetWeight.diagram P F)) (hc : IsLimitCone c)

/-- 概要：正本の G8 比較のうち、実切断空間から指定極限の Hom への後段。
方針：同じ切断錐の頂点比較、宇宙変更、表現の頂点比較、表現可能値の比較を合成する。
規約：新しい同値へ置き換えない。使われ方：切断制限と後合成の全族比較。 -/
def setWeightSectionsLimitTail :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (coherentSpaceSectionsObject (SetWeight.diagram P (F ≫ (spaceTensorData hE M).hom))).obj)
      (Basic.pinchedHom M c.vertex) := by
  let t := spaceTensorData hE M
  let g := SetWeight.diagram P (F ≫ t.hom)
  have hg : IsLimitCone (mapJoinCone t.hom c) :=
    mapJoinCone_isLimit_of_adjunction t.adjunction c hc
  let hs := sectionsLimitValueEquivalence g (mapJoinCone t.hom c) hg
  exact hs.isQCatEquivalence.ulift.choose.trans
    ((SetWeight.spaceUniverseValueEquivalence (t.hom.app _ c.vertex)).trans
      ((SetWeight.spaceValueEquivalence (t.represents.app (ULift.up c.vertex))).symm.trans
        (covariantRepresentableValueEquivalence M c.vertex)))

/-- 概要：正本の比較の順射は、元の随伴比較・切断比較・後段の順射の合成そのもの。
方針：正本と因子の定義を展開し、合成順序をそろえる。
規約：写像の厳密な等式。使われ方：別の比較で自然性を代用しないための接続。 -/
lemma tensorSpaceFunctor_setWeightHomNatural_hom_factor :
    (SetWeight.tensorSpaceFunctor_setWeightHomNatural P hE M F c hc).hom =
      (tensorSpaceFunctor_diagramHom hE M (spaceDiagram P) F).hom ≫
        (SetWeight.sectionsEquivalenceNatural P (F ≫ (spaceTensorData hE M).hom)).hom ≫
          (setWeightSectionsLimitTail P hE M F c hc).hom := by
  simp only [SetWeight.tensorSpaceFunctor_setWeightHomNatural,
    setWeightSectionsLimitTail, sectionsLimitValueEquivalence, QCatEquivalence.trans,
    Category.assoc]

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
