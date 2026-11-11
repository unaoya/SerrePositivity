module

public import SerrePositivity.KST.LocalizingInvariants.VertexIsoPath
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyNatTransPrecomposition
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：指定頂点同型による図式移送の自然変換と、元の同型を持つ各成分。
方針：延長した path 全族の円柱を読み、その頂点の辺を指定した代表へ照合する。
規約：自然性は全図式上で保持。使われ方：積同値への移送後の四辺の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DiagramVertexPaths
variable {K X : SSet.{u}} [Quasicategory X] {F : K ⟶ X}

def ofIso (a : ∀ v : K _⦋0⦌, Σ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) v) x) :
    DiagramVertexPaths F where
  path v := VertexIsoPath.path (a v).2
  source v := VertexIsoPath.path_source (a v).2

namespace Extension
variable {d : DiagramVertexPaths F} (w : d.Extension)

def homotopy : SSet.Homotopy F w.target where
  h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy (w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy (w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).h₀.trans w.source
  h₁ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy (w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy (w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).rel

lemma homotopy_vertex_edge (v : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge w.homotopy v).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X).app (Opposite.op ⦋0⦌) (d.path v)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHomotopy (w.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)) v).edge = _
  rw [arrowFamilyHomotopy_vertex_edge]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X).app _ (w.family.app _ v)) = _
  rw [w.family_vertex]

def naturalTransformation : (hoFunctor.map F).toFunctor ⟶ (hoFunctor.map w.target).toFunctor :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints w.homotopy.h w.homotopy.h₀ w.homotopy.h₁

lemma target_vertex_ofIso
    (a : ∀ v : K _⦋0⦌, Σ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) v) x)
    (w : (ofIso a).Extension) (v : K _⦋0⦌) :
    w.target.app (Opposite.op ⦋0⦌) v = (a v).1 :=
  (w.target_vertex v).trans (VertexIsoPath.path_target (a v).2)

lemma naturalTransformation_component_ofIso
    (a : ∀ v : K _⦋0⦌, Σ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) v) x)
    (w : (ofIso a).Extension) (v : K _⦋0⦌) :
    Arrow.mk (w.naturalTransformation.app (HomotopyCategory.mk v)) =
      Arrow.mk (a v).2.hom := by
  rw [naturalTransformation, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyNatTransOfEndpoints_app_arrow, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTrans_app]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge w.homotopy v).edge =
      (VertexIsoPath.edge (a v).2).edge := by
    rw [w.homotopy_vertex_edge]
    exact VertexIsoPath.path_edge (a v).2
  have h := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (((Truncated.Edge.id (X := (truncation 2).obj K) v).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
      ((truncation 2).map w.homotopy.h)) (VertexIsoPath.edge (a v).2).toTruncated he
  exact h.trans (congrArg Arrow.mk (VertexIsoPath.edge_hom (a v).2))

end Extension
end SerrePositivity.KST.LocalizingInvariants.DiagramVertexPaths
