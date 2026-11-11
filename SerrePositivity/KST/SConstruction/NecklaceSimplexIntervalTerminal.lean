module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceSimplexIntervalFactor
public import SerrePositivity.KST.SConstruction.SimplexBeadCubicalMapping
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # 元の標準単体の任意区間の bead の終対象性
概要：元の a≤b の間の区間 bead は、同じ固定端点の元の全 necklace 図式の終対象。
方針：元の全 augmentation の区間因子を一 bead の逆同型へ送り、単射性で一意性を得る。
規約：一点区間と全高次単体を保持。使われ方：任意区間の cubical/Serre Hom 計算。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet

/-- 元の一 bead の始零単体は、元の零番頂点から作った零単体そのもの。 -/
lemma simplexBeadFirstVertex_eq_standard (d : ℕ) :
    simplexBeadFirstVertex.{u} d = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext rfl

/-- 元の一 bead の終零単体は、元の最後の番号から作った零単体そのもの。 -/
lemma simplexBeadLastVertex_eq_standard (d : ℕ) :
    simplexBeadLastVertex.{u} d = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last d) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex_ext rfl

/-- 元の一 bead の逆同型は、元の零番頂点を同じ始零単体へ戻す。 -/
lemma simplexBeadIso_inv_first (d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} d).inv.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex 0) =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single d).firstVertex := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single d).vertexEquiv.injective
  rfl

/-- 元の一 bead の逆同型は、元の最後の頂点を同じ終零単体へ戻す。 -/
lemma simplexBeadIso_inv_last (d : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} d).inv.app _
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (Fin.last d)) = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single d).lastVertex := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single d).vertexEquiv.injective
  rfl

/-- 元の標準単体の区間 [a,b] 全体を、同じ両端を持つ一 bead として読む。 -/
def necklaceInSimplexInterval {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) where
  necklace := necklaceBead (b.val - a.val)
  map := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab
  map_first := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab).app _)
    (simplexBeadFirstVertex_eq_standard _)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap_first a b hab)
  map_last := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab).app _)
    (simplexBeadLastVertex_eq_standard _)).trans (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap_last a b hab)

/-- 元の区間 bead の augmentation は単射。 -/
instance necklaceInSimplexInterval_map_mono {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    Mono (necklaceInSimplexInterval.{u} a b hab).map :=
  inferInstanceAs (Mono ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab))

/-- 元の任意の augmentation から、元の区間 bead 全体への実可換三角形。 -/
def necklaceInToSimplexInterval {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :
    T ⟶ necklaceInSimplexInterval a b hab where
  necklaceHom :=
    { map := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv
      map_first := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_first T)).trans (simplexBeadIso_inv_first _)
      map_last := (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv.app _)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_last T)).trans (simplexBeadIso_inv_last _) }
  w := by
    change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor T ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).inv) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalMap a b hab) = T.map
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexIntervalFactor_comp T hab

/-- 元の区間全体への可換三角形は、全ての高次単体で一意。 -/
lemma necklaceInSimplexInterval_hom_ext {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    {T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)}
    (f g : T ⟶ necklaceInSimplexInterval a b hab) : f = g :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInHom.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceHom.ext
    ((cancel_mono (necklaceInSimplexInterval a b hab).map).1 (f.w.trans g.w.symm)))

/-- 元の区間 bead 全体は、同じ固定端点の元の全 necklace 図式の終対象。 -/
def necklaceInSimplexInterval_isTerminal {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    IsTerminal (necklaceInSimplexInterval.{u} a b hab) :=
  IsTerminal.ofUniqueHom (necklaceInToSimplexInterval a b hab)
    (fun _ f => necklaceInSimplexInterval_hom_ext a b hab f _)

end SerrePositivity.KST.SConstruction
