module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorNaturality

/-!
模型。文献の定義との比較は後で
# 異なる複体の有限テンソル族

概要：Berger–Moerdijk §1 の全入力への合成に現れる有限個の異なる複体をテンソルする。
方針：右括弧のテンソルを再帰で定義し、最後の一因子を分離する同型を構成する。
規約：空の族はテンソル単位。同一対象の族は既存の反復テンソルに一致する。
使われ方：部分合成から全入力へのオペラッド合成を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：有限族の右括弧テンソル（Berger–Moerdijk §1）。
方針：先頭の因子と残りの有限族で再帰する。
規約：空の族をテンソル単位とする。
使われ方：各 arity が異なる内側演算のテンソルを表す。 -/
def tensorFamily : (n : ℕ) → (Fin n → Complex A) → Complex A
  | 0, _ => 𝟙_ (Complex A)
  | n + 1, V => V 0 ⊗ tensorFamily n (fun i => V i.succ)

/-- 概要：有限族の各因子の射が誘導するテンソル射（Berger–Moerdijk §1）。
方針：先頭の射と残りの族のテンソル射を再帰的にテンソルする。
規約：空の族では恒等射。
使われ方：全入力へのオペラッド合成の自然性を述べる。 -/
def tensorFamilyMap : ∀ (n : ℕ) {V W : Fin n → Complex A},
    (∀ i, V i ⟶ W i) → (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n W)
  | 0, _, _, _ => 𝟙 _
  | n + 1, _V, _W, f => f 0 ⊗ₘ tensorFamilyMap n (fun i => f i.succ)

/-- 概要：有限テンソル族の射は恒等射を保つ（Berger–Moerdijk §1）。
方針：族の長さに関する帰納法とテンソルの恒等射則を使う。
規約：空の族も含む。
使われ方：多変数のテンソル関手を構成する。 -/
@[simp]
lemma tensorFamilyMap_id (n : ℕ) (V : Fin n → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => 𝟙 (V i)) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (𝟙 (V 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => 𝟙 (V i.succ))) = _
    rw [ih, tensorHom_id, id_whiskerRight]
    rfl

/-- 概要：有限テンソル族の射は合成を保つ（Berger–Moerdijk §1）。
方針：族の長さに関する帰納法とテンソル射の合成則を使う。
規約：三つの族の添字集合を固定する。
使われ方：全入力への合成の自然性を因子ごとに扱う。 -/
lemma tensorFamilyMap_comp (n : ℕ) {V W Z : Fin n → Complex A}
    (f : ∀ i, V i ⟶ W i) (g : ∀ i, W i ⟶ Z i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i ≫ g i) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n g := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change ((f 0 ≫ g 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.succ ≫ g i.succ)) = _
    rw [ih]
    exact (tensorHom_comp_tensorHom (f 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => f i.succ))
      (g 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => g i.succ))).symm

/-- 概要：一定の複体の有限テンソル族は既存のテンソル冪に等しい（Berger–Moerdijk §1）。
方針：両定義の同じ再帰を比較する。
規約：等式は対象の等式であり新しいテンソル構造を導入しない。
使われ方：オペラッドの一般の合成と代数の入力を比較する。 -/
lemma tensorFamily_const (K : Complex A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun _ => K) = _root_.SerrePositivity.TensorPowers.power K n := by
  induction n with
  | zero => rfl
  | succ n ih => change K ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun _ => K) = K ⊗ _root_.SerrePositivity.TensorPowers.power K n; rw [ih]

/-- 概要：有限テンソル族の最後の因子を分離する同型（Berger–Moerdijk §1）。
方針：結合子と単位子を使い、長さに関する帰納法で構成する。
規約：前半の族は `Fin.castSucc` による制限。
使われ方：最後の入力から順に演算を代入する再帰に用いる。 -/
def tensorFamilySplitLast : ∀ (n : ℕ) (V : Fin (n + 1) → Complex A),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⊗ V (Fin.last n)
  | 0, V => (ρ_ (V 0)) ≪≫ (λ_ (V 0)).symm
  | n + 1, V =>
    whiskerLeftIso (V 0) (tensorFamilySplitLast n (fun i => V i.succ)) ≪≫
      (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ)) (V (Fin.last (n + 1)))).symm

/-- 概要：同じ複体への射族を有限テンソルしてテンソル冪へ送る（Berger–Moerdijk §1）。
方針：指定した入力ごとの生成射を先頭から順にテンソルする。
規約：空の族ではテンソル単位の恒等射を取る。
使われ方：Schur 対象の入力ごとの生成射を一般の有限テンソルの補題へ接続する。 -/
def tensorFamilyGenerator {ι : Type} (X : Complex A) (D : ι → Complex A) (e : ∀ i, D i ⟶ X) :
    ∀ (n : ℕ) (s : Fin n → ι),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (s i)) ⟶ _root_.SerrePositivity.TensorPowers.power X n
  | 0, _ => 𝟙 _
  | n + 1, s => e (s 0) ⊗ₘ tensorFamilyGenerator X D e n (fun i => s i.succ)

/-- 概要：生成射の有限テンソルは添字の再パラメータ化と両立する（Berger–Moerdijk §1）。
方針：有限族の長さに関する帰納法で各入力の添字の合成を展開する。
規約：二つの添字型はともに小さい。
使われ方：有限全単射で添字付けた生成射を arity で添字付けた生成射と比較する。 -/
lemma tensorFamilyGenerator_reindex {ι κ : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (r : κ → ι) (n : ℕ) (s : Fin n → κ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun i => r (s i)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X (fun i => D (r i)) (fun i => e (r i)) n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (e (r (s 0)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun i => r (s i.succ))) = _
    rw [ih]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
