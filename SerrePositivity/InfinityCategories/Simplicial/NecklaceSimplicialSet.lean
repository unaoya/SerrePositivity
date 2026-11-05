module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! # 元の necklace の単体集合
概要：内部 joint を跨ぐ単体を除いた標準単体の部分複体として necklace を作る。
方針：全頂点対による bead 条件は前合成で保存される。
規約：すべての高次単体を保つ。使われ方：全端点保存写像を持つ necklace 圏。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
namespace NecklaceShape
open _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open CategoryTheory Opposite _root_.Simplicial SSet

/-- 元の necklace を、同じ全頂点の標準単体内の部分複体として作る。 -/
def subcomplex (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : (Δ[T.vertexMax] : SSet.{u}).Subcomplex where
  obj d := {x | T.Allows (stdSimplex.objEquiv x).toOrderHom}
  map f x hx := by
    intro i j k hk
    exact hx (f.unop.toOrderHom i) (f.unop.toOrderHom j) k hk

/-- 元の necklace の実単体集合。 -/
def carrier (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : SSet.{u} := T.subcomplex.toSSet

/-- 元の necklace と標準単体の間の単体的包含。 -/
def inclusion (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : T.carrier.{u} ⟶ Δ[T.vertexMax] := T.subcomplex.ι

/-- 元の包含は全単体で単射。 -/
instance inclusion_mono (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : Mono T.inclusion.{u} :=
  inferInstanceAs (Mono T.subcomplex.ι)

/-- 元の各頂点を、necklace 内の定値単体として与える。 -/
def constantSimplex (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) (v : T.Vertex) (n : ℕ) : T.carrier.{u} _⦋n⦌ :=
  ⟨stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (OrderHom.const _ v)),
    T.allows_const v n⟩

/-- 元の始頂点を零単体として読む。 -/
def firstVertex (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : T.carrier.{u} _⦋0⦌ := T.constantSimplex T.first 0

/-- 元の終頂点を零単体として読む。 -/
def lastVertex (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : T.carrier.{u} _⦋0⦌ := T.constantSimplex T.last 0

/-- 標準単体一つの necklace は、元の標準単体全体を含む。 -/
lemma single_subcomplex_top (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).subcomplex.{u} = ⊤ := by
  apply top_unique
  intro d x hx
  exact _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single_allows n d.unop.len _

end NecklaceShape
end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrier (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.carrier := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrier

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.constantSimplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.constantSimplex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.constantSimplex

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.firstVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.firstVertex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.firstVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.inclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.inclusion := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.inclusion_mono (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.inclusion_mono := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.inclusion_mono

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.lastVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.lastVertex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.lastVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.single_subcomplex_top := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single_subcomplex_top

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.subcomplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.subcomplex := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.subcomplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.subcomplex._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.subcomplex._proof_1
