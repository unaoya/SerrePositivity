module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacent
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurInputNaturality

/-!
模型。文献の定義との比較は後で
# 有限テンソルの隣接交換と入力の生成射

概要：Berger–Moerdijk §1 の外側等変性で、異なる入力の生成射と隣接交換を両立させる。
方針：添字の等式による生成射の移送と、三因子の交換の自然性を用いる。
規約：生成射の終域は同じ複体とし、交換後のテンソル冪には既存の Koszul 交換を用いる。
使われ方：自由代数の外側等変性を生成射上で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

/-- 概要：有限テンソルの生成射は添字族の等式と両立する（Berger–Moerdijk §1）。
方針：添字の等式で二つの族を同一視する。
規約：始域の比較の等式の射を明示する。
使われ方：隣接交換の添字の具体的な表示を生成射に反映する。 -/
lemma tensorFamilyGenerator_index_eq {I : Type} (X : Complex A) (D : I → Complex A)
    (e : ∀ i, D i ⟶ X) (n : ℕ) {s t : Fin n → I} (h : s = t) :
    eqToHom (congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (s i))) h) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n t = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s := by
  subst t
  exact Category.id_comp _

/-- 概要：同じ対象に比較した二つの等しい添字族の生成射は一致する（Berger–Moerdijk §1）。
方針：添字族の等式で同一視し、比較の等式の証明の一意性を使う。
規約：二つの対象の比較の等式の射を明示する。
使われ方：隣接交換の再帰で、同じ置換の異なる表示の移送を比較する。 -/
lemma tensorFamilyGenerator_compare {I : Type} (X : Complex A) (D : I → Complex A)
    (e : ∀ i, D i ⟶ X) (n : ℕ) {s t : Fin n → I} (h : s = t)
    {Z : Complex A} (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (s i)) = Z)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => D (t i)) = Z) :
    eqToHom ht.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n t =
      eqToHom hs.symm ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s := by
  subst t
  rfl

/-- 概要：最初の二つの添字を入れ替える有限族（Berger–Moerdijk §1）。
方針：先頭を 1、次を 0 とし、残りは同じ位置を返す。
規約：添字の表示として `Fin.cases` を使う。
使われ方：隣接互換の対象の比較の射と生成射の移送を同定する。 -/
def tensorFirstSwapIndex (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  fun i => Fin.cases 1 (fun j => Fin.cases 0 (fun k => k.succ.succ) j) i

/-- 概要：最初の二つの添字を入れ替える族は最初の隣接互換である（Berger–Moerdijk §1）。
方針：先頭、次、残りの位置に分けて値を比較する。
規約：隣接互換は既存の Coxeter 系のものを使う。
使われ方：有限テンソルの先頭の交換の計算則を生成射に反映する。 -/
lemma tensorFirstSwapIndex_eq (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n = fun i => adjacentTransposition (0 : Fin (n + 1)) i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_zero n).symm
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_one n).symm
    · exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_tail n j).symm

set_option maxHeartbeats 500000 in
-- 有限添字の cases と対象の比較の定義を正規化するため、この宣言だけ上限を増やす。
/-- 概要：先頭交換後の対象の比較の射を生成射に合成すると、交換した二つの生成射を得る（Berger–Moerdijk §1）。
方針：隣接互換を明示した添字族へ書き換え、生成射の添字の等式の移送を適用する。
規約：最後の n 個の入力の順序は保持する。
使われ方：先頭交換の自然性を入力の生成射の式へ接続する。 -/
lemma tensorFamilyGenerator_firstSwap_transport (X : Complex A)
    (n : ℕ) (V : Fin (n + 2) → Complex A) (e : ∀ i, V i ⟶ X) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n V).symm ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X V e (n + 2)
        (fun i => adjacentTransposition (0 : Fin (n + 1)) i) =
      e 1 ⊗ₘ (e 0 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X V e n (fun i => i.succ.succ)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_index_eq X V e (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq n)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex, Fin.cases_zero, Fin.cases_succ] at h
  exact h

/-- 概要：先頭二因子の交換は入力の生成射と両立する（Berger–Moerdijk §1）。
方針：対象の移送の計算則と三因子の交換の自然性を使う。
規約：終域の交換は既存の反復テンソル上の Koszul 交換。
使われ方：自由代数の外側等変性の先頭の隣接互換の場合に用いる。 -/
lemma tensorFamilySwapFirstIso_generator (X : Complex A)
    (n : ℕ) (V : Fin (n + 2) → Complex A) (e : ∀ i, V i ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n V).hom ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X V e (n + 2)
        (fun i => adjacentTransposition (0 : Fin (n + 1)) i) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X V e (n + 2) (fun i => i) ≫ (swapFirstIso X n).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_firstSwap_transport]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality (e 0) (e 1)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X V e n (fun i => i.succ.succ))).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
