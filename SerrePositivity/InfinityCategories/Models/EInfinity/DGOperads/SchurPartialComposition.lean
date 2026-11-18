module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Schur
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# Schur 対象への部分合成と対称群の関係

概要：Berger–Moerdijk §1 の部分合成が Schur の同時置換の関係を保つことを証明する。
方針：内側・外側の等変性で係数の置換を出力へ移し、Schur 余極限の関係を使う。
規約：arity 0 の代入も含み、入力の置換には Koszul 符号を含める。
使われ方：全入力への合成を反復して自由代数の演算を降ろす際の一段となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

private lemma tensor_intertwining {X Y Z W : Complex A} (f f' : X ⟶ Y) (q : Y ⊗ Z ⟶ W)
    (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z)
    (hf : a ≫ f = f' ≫ b) (hq : (b ⊗ₘ c) ≫ q = q) :
    (a ⊗ₘ c) ≫ (f ▷ Z) ≫ q = (f' ▷ Z) ≫ q := by
  have h : (a ⊗ₘ c) ≫ (f ⊗ₘ 𝟙 Z) = (f' ⊗ₘ 𝟙 Z) ≫ (b ⊗ₘ c) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hf]
  rw [← tensorHom_id f, ← tensorHom_id f', ← Category.assoc, h, Category.assoc, hq]

/-- 概要：部分合成した演算と入力を Schur 対象に送る（Berger–Moerdijk §1）。
方針：二つの係数を部分合成し、結果を Schur の標準生成射に入れる。
規約：挿入位置を固定し、出力 arity は m+n。
使われ方：全入力への代入を一段ずつ coinvariant と両立させる。 -/
def schurPartialGenerator (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (m n : ℕ) (i : Fin (m + 1)) :
    (P.arity (m + 1) ⊗ P.arity n) ⊗ power K (m + n) ⟶
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K :=
  (P.comp m n i ▷ power K (m + n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (m + n)

/-- 概要：部分合成の内側置換と入力の同時置換は Schur 対象で消える（Berger–Moerdijk §1）。
方針：部分合成の内側等変性で出力係数を置換し、Schur の diagonal 関係を適用する。
規約：出力入力の置換は挿入区間内だけに作用する。
使われ方：自由代数の作用の各内側入力についての coinvariant 関係を証明する。 -/
lemma schurPartialGenerator_inner_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (i : Fin (m + 1)) (τ : Equiv.Perm (Fin n)) :
    ((P.arity (m + 1) ◁ P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n τ)) ⊗ₘ
      (permutationAction K (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ)).asIso.hom) ≫
        P.schurPartialGenerator K m n i = P.schurPartialGenerator K m n i := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.tensor_intertwining (P.comp m n i) (P.comp m n i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (m + n))
    _ _ _ (P.inner_equivariance m n i τ) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_diagonal A P.sequence K (m + n) _)

/-- 概要：外側置換は挿入位置を移した部分合成と Schur 対象で一致する（Berger–Moerdijk §1）。
方針：部分合成の外側等変性で置換を出力へ移し、Schur の diagonal 関係を適用する。
規約：挿入区間の内部の順序を保ち、外側の残りの入力を置換する。
使われ方：自由代数の作用と外側の対称群作用を両立させる。 -/
lemma schurPartialGenerator_outer_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) :
    ((P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ▷ P.arity n) ⊗ₘ
      (permutationAction K (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)).asIso.hom) ≫
        P.schurPartialGenerator K m n (σ i) = P.schurPartialGenerator K m n i := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.tensor_intertwining (P.comp m n (σ i)) (P.comp m n i)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (m + n)) _ _ _ (P.outer_equivariance m n i σ)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_diagonal A P.sequence K (m + n) _)

/-- 概要：最後の入力への挿入では内側置換を右ブロックの置換として扱える（Berger–Moerdijk §1）。
方針：一般の内側等変性に、挿入区間の置換とブロック置換の同定を適用する。
規約：前方の m 個の入力は固定する。
使われ方：全入力への合成の最後の入力からの帰納法に用いる。 -/
lemma schurPartialGenerator_last_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (m n : ℕ) (τ : Equiv.Perm (Fin n)) :
    ((P.arity (m + 1) ◁ P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n τ)) ⊗ₘ
      (permutationAction K (m + n)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin m)) τ)).asIso.hom) ≫
        P.schurPartialGenerator K m n (Fin.last m) =
          P.schurPartialGenerator K m n (Fin.last m) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_last] using
    P.schurPartialGenerator_inner_equivariance K m n (Fin.last m) τ

/-- 概要：Schur 対象への部分合成は底の複体射に関して自然である（Berger–Moerdijk §1）。
方針：固定した部分合成の係数射と入力の射を交換し、Schur 生成射の自然性を適用する。
規約：外側・内側の arity と挿入位置を固定する。
使われ方：反復する部分合成から自由代数関手の作用を構成する。 -/
lemma schurPartialGenerator_naturality (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K L : Complex A} (f : K ⟶ L)
    (m n : ℕ) (i : Fin (m + 1)) :
    ((P.arity (m + 1) ⊗ P.arity n) ◁ _root_.SerrePositivity.TensorPowers.map f (m + n)) ≫
      P.schurPartialGenerator L m n i =
        P.schurPartialGenerator K m n i ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f := by
  change (_ ◁ _root_.SerrePositivity.TensorPowers.map f (m + n)) ≫
    (P.comp m n i ▷ power L (m + n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence L (m + n) =
      ((P.comp m n i ▷ power K (m + n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (m + n)) ≫ _
  rw [whisker_exchange_assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality, id_tensorHom]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
