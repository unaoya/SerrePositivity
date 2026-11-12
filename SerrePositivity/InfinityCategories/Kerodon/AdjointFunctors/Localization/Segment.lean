module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Lean.Elab.Tactic.Omega

/-!
# 同方向の列の有限区間の合成

概要：zigzag の同方向の連続区間を、空区間も含めて一つの射へ合成する。
方針：元の圏または反対圏の合成可能射列を構成し、その両端の射を使う。
規約：後ろ向きの合成の弱同値性は元の射の類の乗法性だけから導く。
使われ方：語の単調写像の各 fiber の圧縮。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 元の語の指定する連続区間の各頂点。 -/
def index (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (k : Fin (q.val - p.val + 1)) : Fin (w.length + 1) :=
  ⟨p.val + k.val, by have := q.isLt; omega⟩

@[simp] lemma index_zero (p q : Fin (w.length + 1)) (hpq : p ≤ q) :
    index p q hpq 0 = p := by apply Fin.ext; simp [index]

@[simp] lemma index_last (p q : Fin (w.length + 1)) (hpq : p ≤ q) :
    index p q hpq (Fin.last (q.val - p.val)) = q := by
  apply Fin.ext
  exact Nat.add_sub_of_le hpq

/-- 同方向の列を元の圏または反対圏の合成可能射列にする。 -/
def chain (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    ComposableArrows (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.category d C) (q.val - p.val) :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex (index p q hpq k))) (fun k => by
      let i : Fin w.length := ⟨p.val + k.val, by have := q.isLt; have := k.isLt; omega⟩
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i (hd i (by dsimp [i]; omega) (by
        dsimp [i]
        have := k.isLt
        omega)))

/-- 指定方向の連続区間の同じ両端を結ぶ合成射。 -/
def map (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex q) :=
  eqToHom (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex k)) (index_zero p q hpq).symm) ≫
    (chain d S p q hpq hd).hom ≫
      eqToHom (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex k)) (index_last p q hpq))

/-- 乗法的な射の類は、等式だけによる端点の移送を含む。 -/
lemma eqToHom_mem [W.ContainsIdentities] {A B : C} (h : A = B) : W (eqToHom h) := by
  cases h
  exact W.id_mem _

/-- 各隣接射が指定類にあれば、元の射列の全射も同じ類に入る。 -/
lemma chain_map_mem {D : Type*} [Category D] (V : MorphismProperty D) [V.IsMultiplicative]
    {n : ℕ} (F : ComposableArrows D n)
    (hF : ∀ (i : ℕ) (hi : i < n), V (F.map' i (i + 1))) : V F.hom := by
  have aux : ∀ j : ℕ, ∀ (hj : j ≤ n), V (F.map' 0 j (Nat.zero_le _) hj) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [F.map'_self 0 hj]
      exact V.id_mem _
    | succ j hj =>
      intro hjn
      rw [F.map'_comp 0 j (j + 1) (by omega) (by omega) hjn]
      exact V.comp_mem _ _ (hj (by omega)) (hF j (by omega))
  exact aux n le_rfl

/-- 同方向の合成に課される元の条件は、空区間も含めて保持される。 -/
lemma map_allowed [W.IsMultiplicative] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.allowed d W (map d S p q hpq hd) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.allowed d W).comp_mem
  · exact eqToHom_mem _
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.allowed d W).comp_mem
    · apply chain_map_mem
      intro k hk
      rw [chain, ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow_allowed _ _ _ _
    · exact eqToHom_mem _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment
