module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback

/-! # 標準単体の join の包含の計算

概要：標準単体の join の左右の包含を有限順序写像として評価する。
方針：標準単体への射が頂点で決まることと、join の符号化の左右の値を用いる。
規約：HTT §1.2.8・§1.2.13。使われ方：N7c の cospan の二セルの成分回収。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：標準単体への二つの射は全ての零単体で一致すれば等しい。
方針：任意の単体の各頂点への制限に自然性を適用する。
規約：HTT §1.2.8。使われ方：join の標準単体への比較を頂点に帰着する。 -/
lemma hom_to_stdSimplex_ext_vertices {X : SSet.{u}} {n : ℕ}
    {f g : X ⟶ Δ[n]} (h : ∀ x : X _⦋0⦌, f.app _ x = g.app _ x) : f = g := by
  apply SSet.hom_ext
  intro m
  rcases m with ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  let α := SimplexCategory.const ⦋0⦌ ⦋m⦌ i
  have hf := congrArg (fun F => (F s) 0) (f.naturality α.op)
  have hg := congrArg (fun F => (F s) 0) (g.naturality α.op)
  change (f.app _ (X.map α.op s)) 0 = (f.app _ s) i at hf
  change (g.app _ (X.map α.op s)) 0 = (g.app _ s) i at hg
  exact hf.symm.trans ((congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ => z 0) (h _)).trans hg)

/-- 概要：join から標準単体への射は左右の包含での値により決まる。
方針：頂点を左右のいずれかに分け、標準単体への射の頂点による外延性を使う。
規約：HTT §1.2.8。使われ方：join の面の比較の左右別の検証。 -/
lemma join_hom_to_stdSimplex_ext {K L : SSet.{u}} {n : ℕ}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L ⟶ Δ[n]} (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ g) : f = g := by
  apply hom_to_stdSimplex_ext_vertices
  intro s
  rcases s with ⟨ℓ, a, b⟩
  fin_cases ℓ
  · cases a
    exact congrArg (fun F => F.app (op ⦋0⦌) b) hr
  · cases b
    exact congrArg (fun F => F.app (op ⦋0⦌) a) hl

/-- 概要：標準 join の左の頂点は同じ番号で連結先へ入る。
方針：値を保つ単調写像として定義する。
規約：HTT §1.2.8。使われ方：join の左包含の順序写像。 -/
def joinLeftOrderHom (p q : ℕ) : Fin (p + 1) →o Fin (p + q + 2) where
  toFun i := ⟨i.val, by have := i.isLt; omega⟩
  monotone' _ _ h := h

/-- 概要：標準 join の右の頂点は左の頂点数だけ後ろへ移る。
方針：各値に p+1 を加える単調写像として定義する。
規約：HTT §1.2.8。使われ方：join の右包含の順序写像。 -/
def joinRightOrderHom (p q : ℕ) : Fin (q + 1) →o Fin (p + q + 2) where
  toFun i := ⟨p + 1 + i.val, by have := i.isLt; omega⟩
  monotone' _ _ h := Nat.add_le_add_left h _

/-- 概要：標準単体の join 同型は左包含を番号を保つ包含へ送る。
方針：左区間のみの単体で join の符号化を評価する。
規約：HTT §1.2.8。使われ方：可変因子の面を大きい標準単体の面に直す。 -/
lemma joinStdSimplexIso_inl (p q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[p] : SSet.{u}) Δ[q] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (joinLeftOrderHom p q)) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := p + 1) (q := q + 1) (r := p + 1) (p + 1) (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} p (p + 1) (SSet.yonedaEquiv (𝟙 (Δ[p] : SSet.{u}))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} q ((p + 1) - (p + 1))
      (by simp only [Nat.sub_self, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj]; exact PUnit.unit)) i).val = i.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ i.isLt]
  rfl

/-- 概要：標準単体の join 同型は右包含を p+1 だけ移した包含へ送る。
方針：右区間のみの単体で join の符号化を評価する。
規約：HTT §1.2.8。使われ方：固定した cospan の脚の面の確認。 -/
lemma joinStdSimplexIso_inr (p q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[p] : SSet.{u}) Δ[q] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom =
      SSet.stdSimplex.map (SimplexCategory.mkHom (joinRightOrderHom p q)) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := p + 1) (q := q + 1) (r := q + 1) 0 (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} p 0 PUnit.unit)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} q (q + 1) (SSet.yonedaEquiv (𝟙 (Δ[q] : SSet.{u})))) i).val = p + 1 + i.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ (Nat.zero_le _)]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
