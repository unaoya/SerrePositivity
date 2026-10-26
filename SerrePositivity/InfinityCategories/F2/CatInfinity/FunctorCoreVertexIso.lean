module
public import SerrePositivity.InfinityCategories.Core.OuterHornConverse
public import SerrePositivity.InfinityCategories.F1.Categories.CoreFunctorIso
/-!
概要：同じ関手の頂点と全関手同型を、関手 core の頂点・頂点同型として保持する。
方針：指定可逆辺をそのまま core に入れる。
規約：関手同型の代表を変更しない。使われ方：全試験関手 core による同値検出。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.F2
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

def functorCoreVertex {K X : SSet.{u}} (f : K ⟶ X) :
    (quasicategoryCore ((ihom K).obj X) : SSet.{u}) _⦋0⦌ :=
  ⟨functorVertex f, quasicategoryCore_vertex _⟩

def functorIsoCoreVertexIso {K X : SSet.{u}} [Quasicategory X]
    {f g : K ⟶ X} (h : FunctorIso f g) :
    VertexIso (functorCoreVertex f) (functorCoreVertex g) := by
  let e : Truncated.Edge
      (X := (truncation 2).obj (quasicategoryCore ((ihom K).obj X) : SSet.{u}))
      (functorCoreVertex f) (functorCoreVertex g) :=
    { edge := ⟨h.edge.edge, (quasicategoryCore_mem_edge_iff _).mpr
        ((isInvertibleEdge_congr (e := h.edge) (f := edgeOfSimplex h.edge.edge) rfl).mp
          h.edge_isInvertible)⟩
      src_eq := Subtype.ext h.edge.src_eq
      tgt_eq := Subtype.ext h.edge.tgt_eq }
  have : IsGroupoid (hoFunctor.obj
      (quasicategoryCore ((ihom K).obj X) : SSet.{u})) := kanComplex_ho_isGroupoid _
  letI : IsIso (Truncated.HomotopyCategory.homMk e) := IsGroupoid.all_isIso
    (C := hoFunctor.obj (quasicategoryCore ((ihom K).obj X) : SSet.{u})) _
  exact asIso (Truncated.HomotopyCategory.homMk e)

end SerrePositivity.InfinityCategories.F2
