module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionInsertVertex

/-!
# 解像上の一頂点の追加による実際のホモトピー

概要：恒等射から選んだ頂点との最大値を取る射への単体的ホモトピーを構成する。
方針：旗の変形の引き戻しとの整合を使い、零・一端点を厳密に計算する。
規約：変形が追加する頂点は選んだ頂点だけである。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの解像上の変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 概要：選んだ頂点より小さい点をその頂点へ送り、大きい点は保つ単調写像。
方針：全順序の最大値を使う。
規約：同じ有限頂点集合の自己写像。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の一頂点の追加による変形の終端。 -/
def resolutionUpperVertexMap {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) →o Fin (n + 1) where
  toFun k := max i k
  monotone' _ _ h := max_le_max_left i h

/-- 概要：単位区間の零端点では一頂点の追加は恒等である。
方針：どの段でも頂点を追加せず、既存の旗の正規化の回収則を使う。
規約：旗の次数は任意。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホモトピーの始端。 -/
lemma resolutionInsertVertex_zero {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex F i (OrderHom.const _ 0) = F := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.normalizeResolutionFlag_existing F

/-- 概要：単位区間の一端点での旗は選んだ頂点との最大値による直接像になる。
方針：追加した頂点と元の頂点の場合に分け、切断後の集合と直接像を比較する。
規約：切断で小さい頂点を除くことを含めた厳密な等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホモトピーの終端。 -/
lemma resolutionInsertVertex_one {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex F i (OrderHom.const _ 1) =
      F.pushforward (resolutionUpperVertexMap i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_start]
    rfl
  · funext t
    apply Finset.ext
    intro k
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_sets, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_start]
    change k ∈ (insert i (F.sets t)).filter (max i F.start ≤ ·) ↔
      k ∈ (F.sets t).image (resolutionUpperVertexMap i)
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hk, hl⟩
      rcases hk with rfl | hk
      · exact ⟨F.start, F.start_mem t, max_eq_left (max_le_iff.mp hl).2⟩
      · exact ⟨k, hk, max_eq_right ((le_max_left i F.start).trans hl)⟩
    · rintro ⟨j, hj, rfl⟩
      change (max i j = i ∨ max i j ∈ F.sets t) ∧ max i F.start ≤ max i j
      refine ⟨?_, max_le_max_left i (F.lower t j hj)⟩
      rcases le_total j i with h | h
      · exact Or.inl (max_eq_left h)
      · exact Or.inr ((max_eq_right h).symm ▸ hj)

/-- 概要：変形後の集合の元は選んだ頂点か元の集合の元である。
方針：正規化のフィルターを忘れ、追加した一点の所属を場合分けする。
規約：元の旗で欠けている別の頂点を追加しない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの欠落条件の保存。 -/
lemma resolutionInsertVertex_no_new_vertices {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (n + 1)) (t : Fin (d + 1) →o Fin 2) (r : Fin (d + 1))
    {k : Fin (n + 1)} (hk : k ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex F i t).sets r) :
    k = i ∨ k ∈ F.sets r := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_sets] at hk
  have hm := (Finset.mem_filter.mp hk).1
  by_cases h : t r = 0
  · exact Or.inr (by simpa only [ite_eq_left h] using hm)
  · simpa only [ite_eq_right h, Finset.mem_insert] using hm

/-- 概要：旗の一頂点の追加を解像と単位区間の積からの射にまとめる。
方針：各単体で変形の式を適用し、同時の引き戻しとの整合を使う。
規約：単位区間は標準の Δ[1]。
使われ方：HA 1.3.1.17 の相対的な縮約の単体的ホモトピーの台。 -/
def resolutionInsertHomotopyMap {n : ℕ} (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n where
  app _ := ↾fun x ↦ ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex x.1.down i x.2.down.toOrderHom)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionInsertVertex_pullback x.1.down i x.2.down.toOrderHom
      α.unop.toOrderHom).symm

/-- 概要：解像の恒等射は頂点との最大値による自己写像と単体的にホモトピックである。
方針：一頂点の追加の射の両端を旗の零・一端点の式で計算する。
規約：実際の SSet.Homotopy であり、射のホモトピー類の等式だけではない。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーン上で保存できる変形。 -/
def resolutionInsertHomotopy {n : ℕ} (i : Fin (n + 1)) :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionMap (resolutionUpperVertexMap i)) where
  h := resolutionInsertHomotopyMap i
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact resolutionInsertVertex_zero F.down i
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro F
    apply ULift.ext
    exact resolutionInsertVertex_one F.down i
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.2

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
