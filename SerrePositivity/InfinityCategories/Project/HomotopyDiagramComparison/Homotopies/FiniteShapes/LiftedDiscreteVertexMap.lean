module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.DiscreteCoherentSpaceProducts

/-!
概要：持ち上げた元の離散 nerve 上の図式を、指定した全頂点から構成する。
方針：各離散射列の最初の対象の像を定値単体として取る。
規約：充填性・有限性は不要。元の全頂点を厳密に回収する。
使われ方：反復射影の辺から関手圏内の有限積の全錐を組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の各離散頂点の指定像から、元の全離散図式を構成する。 -/
def liftedDiscreteVertexMap {J : Type u} {X : SSet.{u + 1}}
    (x : J → X _⦋0⦌) : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X where
  app d := ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x (s.down.obj 0).as) d.unop.len
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x (s.down.obj (α.unop.toOrderHom 0)).as) e.unop.len =
      X.map α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x (s.down.obj 0).as) d.unop.len)
    have h := IsDiscrete.eq_of_hom (s.down.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))
    exact (congrArg (fun j : Discrete J ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (x j.as) e.unop.len) h.symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback (x (s.down.obj 0).as) α.unop).symm

/-- 元の指定頂点は、元の全図式から厳密に回収される。 -/
lemma liftedDiscreteVertexMap_vertex {J : Type u} {X : SSet.{u + 1}}
    (x : J → X _⦋0⦌) (j : J) :
    (liftedDiscreteVertexMap x).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) = x j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _

/-- 元の離散図式を全頂点から再構成すると元の図式そのもの。 -/
lemma liftedDiscreteVertexMap_eta {J : Type u} {X : SSet.{u + 1}}
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete J)) ⟶ X) :
    liftedDiscreteVertexMap (fun j ↦ p.app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j)))) = p := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro j
  exact liftedDiscreteVertexMap_vertex _ j.as

/-- 元の全頂点からの図式の構成は、元の射の後合成と厳密に可換。 -/
lemma liftedDiscreteVertexMap_postcomp {J : Type u} {X Y : SSet.{u + 1}}
    (x : J → X _⦋0⦌) (a : X ⟶ Y) :
    liftedDiscreteVertexMap x ≫ a =
      liftedDiscreteVertexMap (fun j ↦ a.app (Opposite.op ⦋0⦌) (x j)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedDiscreteDiagram_ext
  intro j
  change a.app _ ((liftedDiscreteVertexMap x).app _ _) = _
  rw [liftedDiscreteVertexMap_vertex, liftedDiscreteVertexMap_vertex]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
