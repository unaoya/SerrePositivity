module

public import SerrePositivity.EInfinity.Operad.TensorFamilyAdjacentGenerators

/-!
# 尾の隣接交換と Schur 入力の生成射

概要：Berger–Moerdijk §1 の外側等変性に必要な、全ての隣接交換と入力の生成射の両立を証明する。
方針：先頭を固定する置換の移送を計算し、先頭の交換の自然性から尾へ帰納する。
規約：終域では既存の反復テンソルの隣接交換を用いる。
使われ方：Schur 作用の外側等変性を隣接互換について検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

/-- 概要：先頭を固定し、尾に指定した置換を作用させる添字族（Berger–Moerdijk §1）。
方針：先頭は 0 を返し、尾では置換後の添字を一つずらす。
規約：対象の比較に使う計算可能な添字の表示である。
使われ方：尾の置換の対象の移送を生成射へ反映する。 -/
def tensorTailPermutationIndex (n : ℕ) (σ : Equiv.Perm (Fin n)) : Fin (n + 1) → Fin (n + 1) :=
  fun i => Fin.cases 0 (fun j => (σ j).succ) i

/-- 概要：尾の置換の添字族は既存のずらした置換に一致する（Berger–Moerdijk §1）。
方針：先頭と尾に分けて評価する。
規約：ずらした置換は先頭を固定する。
使われ方：隣接互換の再帰の添字を生成射の移送と接続する。 -/
lemma tensorTailPermutationIndex_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    tensorTailPermutationIndex n σ = fun i => shiftPerm σ i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (shiftPerm_zero σ).symm
  · exact (shiftPerm_succ σ j).symm

/-- 概要：尾の置換後の対象の移送は先頭の生成射と尾の生成射へ分かれる（Berger–Moerdijk §1）。
方針：尾の置換を明示した添字族へ書き換え、生成射の添字の移送と再パラメータ化を適用する。
規約：先頭の生成射は変えない。
使われ方：隣接交換の自然性を尾へ帰納する。 -/
lemma tensorFamilyGenerator_shift_transport (X : Complex A) (n : ℕ)
    (V : Fin (n + 1) → Complex A) (e : ∀ i, V i ⟶ X) (σ : Equiv.Perm (Fin n)) :
    eqToHom (tensorFamily_shiftPermutation_obj n V σ).symm ≫
      tensorFamilyGenerator X V e (n + 1) (fun i => shiftPerm σ i) =
        e 0 ⊗ₘ tensorFamilyGenerator X (fun i => V i.succ) (fun i => e i.succ) n σ := by
  have h := tensorFamilyGenerator_index_eq X V e (n + 1) (tensorTailPermutationIndex_eq n σ)
  calc
    _ = e 0 ⊗ₘ tensorFamilyGenerator X V e n (fun i => (σ i).succ) := h
    _ = _ := congrArg (e 0 ⊗ₘ ·) (tensorFamilyGenerator_reindex X V e Fin.succ n σ)

/-- 概要：尾の隣接交換後の生成射は先頭の生成射と尾の生成射に分かれる（Berger–Moerdijk §1）。
方針：ずらした置換の生成射の式を、二つの添字表示の比較で隣接互換へ移す。
規約：対象の比較は専用の補題を用いる。
使われ方：隣接交換の自然性の帰納段階で対象の移送を除く。 -/
lemma tensorFamilyGenerator_adjacentSucc_transport (X : Complex A) (n : ℕ)
    (V : Fin (n + 2) → Complex A) (e : ∀ i, V i ⟶ X) (i : Fin n) :
    eqToHom (tensorFamily_adjacentSucc_obj n V i).symm ≫
      tensorFamilyGenerator X V e (n + 2) (fun j => adjacentTransposition i.succ j) =
        e 0 ⊗ₘ tensorFamilyGenerator X (fun j => V j.succ) (fun j => e j.succ)
          (n + 1) (adjacentTransposition i) := by
  exact (tensorFamilyGenerator_compare X V e (n + 2)
    (congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => fun j => σ j) (shiftPerm_adjacent n i))
    (tensorFamily_shiftPermutation_obj (n + 1) V (adjacentTransposition i))
    (tensorFamily_adjacentSucc_obj n V i)).trans
      (tensorFamilyGenerator_shift_transport X (n + 1) V e (adjacentTransposition i))

/-- 概要：恒等の添字の生成射の有限テンソルは先頭と尾に分かれる（Berger–Moerdijk §1）。
方針：先頭の再帰を展開し、残りの生成射を尾で再パラメータ化する。
規約：有限族の各因子は独立な複体でよい。
使われ方：隣接交換の帰納段階の終域の式を簡約する。 -/
lemma tensorFamilyGenerator_succ_id (X : Complex A) (n : ℕ)
    (V : Fin (n + 1) → Complex A) (e : ∀ i, V i ⟶ X) :
    tensorFamilyGenerator X V e (n + 1) (fun i => i) =
      e 0 ⊗ₘ tensorFamilyGenerator X (fun i => V i.succ) (fun i => e i.succ) n (fun i => i) := by
  exact congrArg (e 0 ⊗ₘ ·) (tensorFamilyGenerator_reindex X V e Fin.succ n (fun i => i))

/-- 概要：反復テンソルの尾の隣接交換は尾の交換の whisker である（Berger–Moerdijk §1）。
方針：既存の隣接交換の定義の尾の場合を評価する。
規約：先頭の因子は固定する。
使われ方：有限テンソル族と反復テンソルの尾の交換を比較する。 -/
lemma tensorPowerAdjacentIso_succ (X : Complex A) (n : ℕ) (i : Fin n) :
    (adjacentIso X (n + 1) i.succ).hom = X ◁ (adjacentIso X n i).hom := rfl

private lemma tail_generator {R X U V Z : Complex A} (a : R ⟶ X) (f : U ⟶ V)
    (g : V ⟶ Z) (h : U ⟶ Z) (q : Z ⟶ Z) (hf : f ≫ g = h ≫ q) :
    (R ◁ f) ≫ (a ⊗ₘ g) = (a ⊗ₘ h) ≫ (X ◁ q) := by
  rw [whiskerLeft_comp_tensorHom, hf, ← tensorHom_comp_whiskerLeft]

/-- 概要：全ての隣接交換は有限テンソルの入力の生成射と両立する（Berger–Moerdijk §1）。
方針：先頭の交換を基底とし、先頭を固定する尾の置換へ帰納する。
規約：交換後の生成射は同じ添字の隣接互換で引き戻す。
使われ方：自由代数の外側等変性で生成射上の入力を並べ替える。 -/
lemma tensorFamilyAdjacentIso_generator (X : Complex A) (n : ℕ)
    (V : Fin (n + 1) → Complex A) (e : ∀ i, V i ⟶ X) (i : Fin n) :
    (tensorFamilyAdjacentIso n V i).hom ≫
      tensorFamilyGenerator X V e (n + 1) (fun j => adjacentTransposition i j) =
        tensorFamilyGenerator X V e (n + 1) (fun j => j) ≫ (adjacentIso X n i).hom := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [tensorFamilyAdjacentIso_zero]
      exact tensorFamilySwapFirstIso_generator X n V e
    · rw [tensorFamilyAdjacentIso_succ, Category.assoc,
        tensorFamilyGenerator_adjacentSucc_transport, tensorFamilyGenerator_succ_id,
        tensorPowerAdjacentIso_succ]
      exact tail_generator (e 0) _ _ _ _ (ih (fun j => V j.succ) (fun j => e j.succ) j)

namespace Operad

/-- 概要：Schur 入力の生成射は各隣接交換と両立する（Berger–Moerdijk §1）。
方針：有限族の一般の生成射の隣接交換の自然性を、Schur 生成射へ適用する。
規約：内側 arity の族を同じ隣接互換で引き戻す。
使われ方：Schur 作用の外側等変性を生成射上で検証する。 -/
lemma schurInputGenerator_adjacent (P : Operad A) (K : Complex A) (n : ℕ)
    (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (tensorFamilyAdjacentIso n (fun j => P.arity (s j) ⊗ power K (s j)) i).hom ≫
      P.schurInputGenerator K (n + 1) (fun j => s (adjacentTransposition i j)) =
        P.schurInputGenerator K (n + 1) s ≫
          (adjacentIso ((schurFunctor A P.sequence).obj K) n i).hom := by
  let X := (schurFunctor A P.sequence).obj K
  let D := fun m => P.arity m ⊗ power K m
  let e := fun m => schurι A P.sequence K m
  have h := tensorFamilyAdjacentIso_generator X n (fun j => D (s j)) (fun j => e (s j)) i
  calc
    _ = (tensorFamilyAdjacentIso n (fun j => D (s j)) i).hom ≫
        tensorFamilyGenerator X (fun j => D (s j)) (fun j => e (s j)) (n + 1)
          (fun j => adjacentTransposition i j) :=
      congrArg ((tensorFamilyAdjacentIso n (fun j => D (s j)) i).hom ≫ ·)
        (tensorFamilyGenerator_reindex X D e s (n + 1) (fun j => adjacentTransposition i j))
    _ = _ := h
    _ = _ := congrArg (· ≫ (adjacentIso X n i).hom)
      (tensorFamilyGenerator_reindex X D e s (n + 1) (fun j => j)).symm

end Operad

end SerrePositivity.EInfinity
