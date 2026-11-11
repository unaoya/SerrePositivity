module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.CoreFunctorIso
/-!
概要：同じ関手の頂点と全関手同型を、関手 core の頂点・頂点同型として保持する。
方針：指定可逆辺をそのまま core に入れる。
規約：関手同型の代表を変更しない。使われ方：全試験関手 core による同値検出。

対応節は Kerodon 5.5（Tag 01YV）。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

def functorCoreVertex {K X : SSet.{u}} (f : K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj X) : SSet.{u}) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

def functorIsoCoreVertexIso {K X : SSet.{u}} [Quasicategory X]
    {f g : K ⟶ X} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (functorCoreVertex f) (functorCoreVertex g) := by
  let e : Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj X) : SSet.{u}))
      (functorCoreVertex f) (functorCoreVertex g) :=
    { edge := ⟨h.edge.edge, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := h.edge) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex h.edge.edge) rfl).mp
          h.edge_isInvertible)⟩
      src_eq := Subtype.ext h.edge.src_eq
      tgt_eq := Subtype.ext h.edge.tgt_eq }
  have : IsGroupoid (hoFunctor.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj X) : SSet.{u})) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid _
  letI : IsIso (Truncated.HomotopyCategory.homMk e) := IsGroupoid.all_isIso
    (C := hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj X) : SSet.{u})) _
  exact asIso (Truncated.HomotopyCategory.homMk e)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
