module
public import SerrePositivity.InfinityCategories.Derived.DGVertexIsoOfH0
public import SerrePositivity.InfinityCategories.F1.Categories.CoreKan

/-!
概要：quasicategory 内の頂点同型を、同じ core の頂点同型へ持ち上げる。
方針：同型を代表する可逆辺を core の一単体として保持する。
規約：全単体作用の存在を頂点同型から推論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded
open scoped Simplicial

/-- 頂点同型の代表辺は同じ core に入り、その中でも可逆になる。 -/
def coreVertexIsoOfVertexIso {X : SSet.{u}} [Quasicategory X]
    {x y : X.obj (Opposite.op ⦋0⦌)} (e : VertexIso (X := X) x y) :
    VertexIso (X := (quasicategoryCore X : SSet))
      ⟨x, quasicategoryCore_vertex _⟩ ⟨y, quasicategoryCore_vertex _⟩ := by
  let a := (homotopyCategory_homMk_surjective x y e.hom).choose
  have ha := (homotopyCategory_homMk_surjective x y e.hom).choose_spec
  have hi : IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  let s : (quasicategoryCore X : SSet).obj (Opposite.op ⦋1⦌) :=
    ⟨a.edge, (quasicategoryCore_mem_edge_iff _).mpr
      ((isInvertibleEdge_congr (e := a) (f := edgeOfSimplex a.edge) rfl).mp hi)⟩
  let b : SSet.Truncated.Edge (X := (truncation 2).obj (quasicategoryCore X : SSet))
      ⟨x, quasicategoryCore_vertex _⟩ ⟨y, quasicategoryCore_vertex _⟩ :=
    { edge := s
      src_eq := Subtype.ext a.src_eq
      tgt_eq := Subtype.ext a.tgt_eq }
  let f : (SSet.HomotopyCategory.mk ⟨x, quasicategoryCore_vertex _⟩ :
      hoFunctor.obj (quasicategoryCore X : SSet)) ⟶
      SSet.HomotopyCategory.mk ⟨y, quasicategoryCore_vertex _⟩ :=
    SSet.Truncated.HomotopyCategory.homMk b
  letI : IsIso f := IsGroupoid.all_isIso (C := hoFunctor.obj (quasicategoryCore X : SSet)) f
  exact asIso f

/-- dg H⁰ の同型は、同じ dg nerve の native core の頂点同型を与える。 -/
def dgCoreVertexIsoOfH0 (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
    {x y : D}
    (e : (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x) ≅
      (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) y)) :
    VertexIso (X := (quasicategoryCore (dgNerve R D) : SSet))
      ⟨DGNerve.Simplex.vertex x, quasicategoryCore_vertex _⟩
      ⟨DGNerve.Simplex.vertex y, quasicategoryCore_vertex _⟩ :=
  coreVertexIsoOfVertexIso (dgVertexIsoOfH0 R D e)

end SerrePositivity.InfinityCategories
