module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceSimplicialSet

/-! # bead 条件を保つ単調写像の単体的作用
概要：有限順序上の写像から、元の necklace 全体の単体的写像を作る。
方針：各単体の全頂点に同じ順序写像を適用する。
規約：端点保存は要求しない。使われ方：wedge の包含と共有頂点への射影。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open SerrePositivity.KST.SConstruction
open _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open CategoryTheory _root_.Simplicial SSet

/-- 全単体の bead 条件を保つ順序写像の、元の実単体集合への作用。 -/
def orderMap {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s)) :
    T.carrier.{u} ⟶ U.carrier.{u} where
  app d := ↾fun s => ⟨stdSimplex.objEquiv.symm
    (SimplexCategory.Hom.mk (f.comp (stdSimplex.objEquiv s.val).toOrderHom)),
    hf s.property⟩
  naturality {d e} a := by
    obtain ⟨⟨n⟩⟩ := d
    obtain ⟨⟨m⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

/-- 元の各単体の全頂点上で、指定した順序写像を回収する。 -/
lemma orderMap_vertex {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s))
    {n : ℕ} (s : T.carrier.{u} _⦋n⦌) (i : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap f hf).app _ s).val i = f (s.val i) := rfl

/-- 定値な元の単体への作用も、同じ順序写像の定値単体。 -/
lemma orderMap_constant {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (f : T.Vertex →o U.Vertex)
    (hf : ∀ {n : ℕ} {s : Fin (n + 1) → T.Vertex}, T.Allows s → U.Allows (f ∘ s))
    (v : T.Vertex) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap f hf).app _ (T.constantSimplex v n) = U.constantSimplex (f v) n := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

end SerrePositivity.InfinityCategories.Simplicial.NecklaceShape

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.orderMap := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.orderMap_constant := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap_constant

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.orderMap_vertex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.orderMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.orderMap._proof_2 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.orderMap._proof_2
