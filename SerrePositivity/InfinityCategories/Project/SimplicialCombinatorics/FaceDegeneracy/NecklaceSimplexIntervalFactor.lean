module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.NecklaceSimplexIntervalOrder

/-! # 元の augmentation の区間標準単体への厳密な因数分解
概要：元の全 necklace の標準単体への写像を、同じ両端の区間を通して一意に分解する。
方針：元の局所頂点番号を標準単体の関手へ送り、全単体の拡張式で元の写像を回収する。
規約：元の全高次単体と可換三角形を保持。使われ方：区間 bead の終対象性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet
variable {n : ℕ} {a b : Fin (n + 1)}
  (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))

/-- 元の局所番号を、元の有限順序の間の単体圏の射として読む。 -/
def necklaceSimplexIntervalHom : ⦋T.necklace.down.vertexMax⦌ ⟶ ⦋b.val - a.val⦌ :=
  SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder T)

/-- 元の全 necklace の augmentation を、元の区間標準単体へ送る因子。 -/
def necklaceSimplexIntervalFactor : T.necklace.down.carrier ⟶ Δ[b.val - a.val] :=
  T.necklace.down.inclusion ≫ stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalHom T)

/-- 元の因子は、全ての高次単体で元の局所頂点番号を回収する。 -/
lemma necklaceSimplexIntervalFactor_apply {m : ℕ} (s : T.necklace.down.carrier _⦋m⦌)
    (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T).app _ s i = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder T (s.val i) := rfl

/-- 元の因子は、元の始頂点を区間の始零単体へ送る。 -/
lemma necklaceSimplexIntervalFactor_first :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T).app _ T.necklace.down.firstVertex =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_first T)

/-- 元の因子は、元の終頂点を区間の終零単体へ送る。 -/
lemma necklaceSimplexIntervalFactor_last :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T).app _ T.necklace.down.lastVertex =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last (b.val - a.val)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_last T)

/-- 元の局所番号の単体圏の射は、区間包含との合成で元の全頂点作用を回収する。 -/
lemma necklaceSimplexIntervalHom_comp (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalHom T ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab =
      SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexOrderHom T.necklace.down T.map) :=
  congrArg (fun q : T.necklace.down.Vertex →o Fin (n + 1) =>
    (SimplexCategory.Hom.mk q : ⦋T.necklace.down.vertexMax⦌ ⟶ ⦋n⦌))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalOrder_comp T hab)

/-- 元の区間因子を元の包含に合成すると、元の全 augmentation が厳密に戻る。 -/
lemma necklaceSimplexIntervalFactor_comp (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab = T.map := by
  have h := ((stdSimplex.{u}).map_comp (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalHom T)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab)).symm.trans
      (congrArg (fun q => stdSimplex.map q) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalHom_comp T hab))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.necklace.down.inclusion ≫ f) h).trans
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexMap_eq_extension T.necklace.down T.map))

/-- 元の区間の単射性から、同じ augmentation の区間因子は一意。 -/
lemma necklaceSimplexIntervalFactor_unique (hab : a ≤ b)
    (f : T.necklace.down.carrier ⟶ Δ[b.val - a.val])
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab = T.map) : f = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T :=
  (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab)).1
    (h.trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_comp T hab).symm)

/-- 元の全可換三角形は、同じ区間因子の間の可換三角形を定める。 -/
lemma necklaceSimplexIntervalFactor_naturality (hab : a ≤ b)
    {U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)}
    (f : T ⟶ U) :
    f.necklaceHom.map ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor U = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab)).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => f.necklaceHom.map ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_comp U hab)).trans
      (f.w.trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_comp T hab).symm))

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
