module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.HornPointJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-! # 任意次元の点上 over 単体と終点固定単体の回収

概要：実 over 単体を、点との join 同型で元の単体集合の一つ上の単体へ移す。
方針：全順序写像への自然性と、終点固定延長の coface 公式を使う。
規約：全次数を同じ定義で扱う。使われ方：一般最後ホーン充填の実 over への回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 任意次元の実 over 単体が指定する、一つ上の元の実単体。 -/
def roofPointSliceSimplex {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) : Δ[n + 1] ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ σ.val

/-- 回収単体の最後の頂点は、元の指定点に固定されている。 -/
lemma roofPointSliceSimplex_fixed {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n) ≫ roofPointSliceSimplex a σ = a := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inr]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ σ.val) = a
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact σ.property

/-- 回収は全次元で実 over 単体を区別する。 -/
lemma roofPointSliceSimplex_injective {n : ℕ} {σ τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌}
    (h : roofPointSliceSimplex a σ = roofPointSliceSimplex a τ) : σ = τ := by
  apply Subtype.ext
  exact (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).mp h

/-- 回収単体は、終点固定延長による全順序写像と可換である。 -/
lemma roofPointSliceSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) ≫ roofPointSliceSimplex a σ =
      roofPointSliceSimplex a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality.{u} α
  have h : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hi, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ σ.val) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) ≫ σ.val)
  rw [← Category.assoc, h, Category.assoc]

/-- 終点固定延長は、全次数の coface を同じ番号の coface へ移す。 -/
lemma roofPointExtend_coface {n : ℕ} (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ i) = SimplexCategory.δ i.castSucc := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  induction j using Fin.lastCases with
  | last =>
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.δ i).toOrderHom
      (Fin.last (n + 1)) = i.castSucc.succAbove (Fin.last (n + 1))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last,
      Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    rfl
  | cast j =>
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom (SimplexCategory.δ i).toOrderHom j.castSucc =
      i.castSucc.succAbove j.castSucc
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    exact Fin.castSucc_succAbove_castSucc.symm

/-- 全ての over 面は、元の回収単体の最終面以外の同じ番号の面となる。 -/
lemma roofPointSliceSimplex_face {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n + 1⦌) (i : Fin (n + 2)) :
    SSet.stdSimplex.δ i.castSucc ≫ roofPointSliceSimplex a σ =
      roofPointSliceSimplex a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).δ i σ) := by
  have h := roofPointSliceSimplex_naturality a (SimplexCategory.δ i) σ
  rw [roofPointExtend_coface] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
