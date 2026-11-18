module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily

/-!
模型。文献の定義との比較は後で
# 同型の有限テンソル生成射

概要：Berger–Moerdijk §1 の生成元による射の比較で使う、有限テンソルした同型の性質を示す。
方針：入力数に関する帰納法でテンソル積の同型保存を使う。
規約：同型性は明示的な仮定として受け取り、大域 instance を追加しない。
使われ方：単位係数と一次の入力からなる生成射の前合成を相殺する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：各入力の生成射が同型なら有限テンソルした生成射も同型である（Berger–Moerdijk §1）。
方針：先頭と残りに分けて帰納し、テンソル積の同型保存を用いる。
規約：空の族の恒等射も含む。
使われ方：自由代数の生成元に関する等式を同型の前合成で検査する。 -/
lemma tensorFamilyGenerator_isIso {ι : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (he : ∀ i, IsIso (e i)) (n : ℕ) (s : Fin n → ι) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n s) := by
  induction n with
  | zero =>
    change IsIso (𝟙 (𝟙_ (Complex A)))
    infer_instance
  | succ n ih =>
    change IsIso (e (s 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun j => s j.succ))
    have := he (s 0)
    have := ih (fun j => s j.succ)
    infer_instance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
