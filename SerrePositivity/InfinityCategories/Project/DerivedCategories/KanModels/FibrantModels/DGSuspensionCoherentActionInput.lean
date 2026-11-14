module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeActionInput
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeEquivalencePathAt

/-!
概要：固定懸垂の全単体作用と、実射作用への端点固定比較を保持する採用入力。
方針：map・vertex・data は元のまま、edge 等号だけを写像空間内の指定同型へ緩める。
規約：模型・I・P・固定 S・ν・K は変更しない。この型の無条件存在は未供給。
使われ方：D-8 e の供給と K-B3 の比較付き反復アダプタ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 元の厳密 vertex 等号だけで正規化した、全作用の実際の dg 入力辺。 -/
def dgSuspensionMappedEdge
    (m : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R)
    (hv : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
      m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone))
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R B (s B).cone)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map m).ofEq (hv A) (hv B)

/-- 採用 B1：vertex は厳密、各実 dg 射との照合は端点固定の指定可逆二胞体。 -/
structure DGSuspensionCoherentActionInput where
  map : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R
  vertex : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    map.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone)
  data : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
    DGKappaSuspensionMapData R A B (s A).cone (s B).cone
  /-- 固定端点の写像空間内の同型なので、両端の成分は動かない。 -/
  edgeIso : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (dgSuspensionMappedEdge R s map vertex f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (data f))))

/-- 元の厳密作用を、map・vertex・実射データを保持して採用入力へ送る。 -/
def DGSuspensionCoherentActionInput.ofStrict (a : DGSuspensionNativeActionInput R s) :
    DGSuspensionCoherentActionInput R s where
  map := a.map
  vertex := a.vertex
  data := a.data
  edgeIso f := by
    have h : dgSuspensionMappedEdge R s a.map a.vertex f =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgKappaSuspensionInputMap R _ _ _ _ (a.data f)) := by
      apply SSet.Edge.ext
      exact a.edge f
    rw [h]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
