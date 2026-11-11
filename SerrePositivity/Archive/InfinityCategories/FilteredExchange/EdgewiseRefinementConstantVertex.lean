module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：退化した元の辺の共通解像の頂点は、元の頂点への定値射である。
方針：Yoneda の退化の式と零単体の定値表示を使う。
規約：元の重みと係数を保持。使われ方：固定 Kan 射での二側補間の値の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の退化辺を共通解像の頂点へ入れると、同じ元の頂点の定値射となる。 -/
lemma edgewiseRefinementVertex_degenerate {X : SSet.{u}} (x : X _⦋0⦌) :
    edgewiseRefinementVertex (X.σ 0 x) = SSet.const x := by
  change (edgewiseWeightIso 0).hom ≫
    SSet.yonedaEquiv.symm (X.map (SimplexCategory.σ (0 : Fin 1)).op x) = _
  rw [← SSet.yonedaEquiv_symm_naturality_left]
  simp only [SSet.yonedaEquiv_symm_zero, Category.assoc, SSet.comp_const]

/-- 同じ定値の共通解像頂点の全退化単体も、重みから元の頂点への定値射。 -/
lemma edgewiseRefinementVertex_degenerate_constant {X : SSet.{u}} (x : X _⦋0⦌) (n : ℕ) :
    PinchedHom.constant (edgewiseRefinementVertex (X.σ 0 x)) n =
      (SSet.const x : edgewiseWeight.obj ⦋n⦌ ⟶ X) := by
  change edgewiseWeight.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫
    edgewiseRefinementVertex (X.σ 0 x) = _
  rw [edgewiseRefinementVertex_degenerate, SSet.comp_const]

end SerrePositivity.InfinityCategories.F2
