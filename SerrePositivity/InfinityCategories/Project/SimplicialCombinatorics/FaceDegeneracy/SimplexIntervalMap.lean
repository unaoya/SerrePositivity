module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexIntervalOrder

/-! # 元の標準単体の頂点と区間の単体的包含
概要：元の二頂点の間の区間を標準単体へ単射に含め、元の全単体と両端を回収する。
方針：元の順序包含を標準単体の関手へ送る。
規約：一点区間も元の頂点へ写す。使われ方：固定端点の区間 bead の augmentation。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet

/-- 元の番号 a の頂点を標準単体の零単体として読む。 -/
def standardSimplexVertex {n : ℕ} (a : Fin (n + 1)) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (OrderHom.const (Fin 1) a))

/-- 元の番号から作った零単体は、元の頂点番号を回収する。 -/
lemma standardSimplexVertex_val {n : ℕ} (a : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u} a 0 = a := rfl

/-- 元の標準単体の零単体は、元の唯一の頂点番号で判定できる。 -/
lemma standardSimplexVertex_ext {n : ℕ} {x y : (Δ[n] : SSet.{u}) _⦋0⦌}
    (h : x 0 = y 0) : x = y := by
  apply stdSimplex.ext
  intro i
  have hi : i = 0 := by apply Fin.ext; omega
  subst i
  exact h

/-- 元の標準単体の全零単体を、元の番号から厳密に回収する。 -/
lemma standardSimplexVertex_eta {n : ℕ} (x : (Δ[n] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (x 0) = x :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext rfl

/-- 元の区間 [a,b] の標準単体から、元の標準単体への単体的包含。 -/
def simplexIntervalMap {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (Δ[b.val - a.val] : SSet.{u}) ⟶ Δ[n] :=
  stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab)

/-- 元の区間の包含は、全ての高次単体で元の順序包含を回収する。 -/
lemma simplexIntervalMap_apply {n m : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (s : (Δ[b.val - a.val] : SSet.{u}) _⦋m⦌) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab).app _ s i = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab (s i) := rfl

/-- 元の区間の単体的包含は単射。 -/
instance simplexIntervalMap_mono {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap.{u} a b hab) := by
  let : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab) :=
    (SimplexCategory.mono_iff_injective
      (f := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab)).mpr
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_injective a b hab)
  exact inferInstanceAs
    (Mono (uliftYoneda.{u}.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom a b hab)))

/-- 元の区間の始零単体は元の a に写る。 -/
lemma simplexIntervalMap_first {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap.{u} a b hab).app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_first a b hab)

/-- 元の区間の終零単体は元の b に写る。 -/
lemma simplexIntervalMap_last {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap.{u} a b hab).app _
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last (b.val - a.val))) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_last a b hab)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
