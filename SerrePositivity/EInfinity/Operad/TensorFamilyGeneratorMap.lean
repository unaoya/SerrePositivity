module

public import SerrePositivity.EInfinity.Operad.TensorFamilyHeadAssembly

/-!
# 有限テンソルの生成射を因子ごとの射として扱う

概要：Berger–Moerdijk §1 の自由代数の入力生成射を有限族の射の自然性へ接続する。
方針：一定の対象の有限テンソルとテンソル冪を同一視する。
規約：空の族ではテンソル単位の恒等射を使う。
使われ方：先頭演算を組み込む射と Schur 入力の生成射の両立を示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一定族とテンソル冪の同一視は先頭因子を保つ（Berger–Moerdijk §1）。
方針：右括弧の再帰を一回評価し、等式による射の証明の一意性を使う。
規約：尾の長さは n。
使われ方：生成射を因子ごとのテンソル射で表す帰納段階に用いる。 -/
lemma tensorFamily_const_succ_hom (X : Complex A) (n : ℕ) :
    eqToHom (tensorFamily_const X (n + 1)) = X ◁ eqToHom (tensorFamily_const X n) := by
  rw [whiskerLeft_eqToHom]

/-- 概要：有限族の生成射は各因子の射のテンソルと一定族の同一視の合成である（Berger–Moerdijk §1）。
方針：族の長さで帰納し、一定族の同一視の先頭での再帰を使う。
規約：添字の型と生成射の族は任意。
使われ方：生成射へ有限テンソル族の自然性を適用する。 -/
lemma tensorFamilyGenerator_asMap {ι : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (n : ℕ) (s : Fin n → ι) :
    tensorFamilyGenerator X D e n s =
      tensorFamilyMap n (fun j => e (s j)) ≫ eqToHom (tensorFamily_const X n) := by
  induction n with
  | zero =>
    simp only [tensorFamilyGenerator, tensorFamilyMap, eqToHom_refl, Category.id_comp]
    rfl
  | succ n ih =>
    change (e (s 0) ⊗ₘ tensorFamilyGenerator X D e n (fun j => s j.succ)) =
      (e (s 0) ⊗ₘ tensorFamilyMap n (fun j => e (s j.succ))) ≫ _
    rw [ih, tensorFamily_const_succ_hom, tensorHom_comp_whiskerLeft]

/-- 概要：先頭の対象と尾のテンソル冪を一つのテンソル冪へ組み込む射（Berger–Moerdijk §1）。
方針：尾を一定の有限テンソル族へ移し、先頭を組み込んでテンソル冪へ戻す。
規約：入力の順序を保ち、尾の長さ m は零でもよい。
使われ方：先頭の Schur 生成射と残りの入力をまとめる。 -/
def tensorFamilyHeadAssemblyToPower (X : Complex A) (m : ℕ) :
    X ⊗ power X m ⟶ power X (1 + m) :=
  (X ◁ eqToHom (tensorFamily_const X m).symm) ≫
    tensorFamilyHeadAssembly m (fun _ => X) ≫ eqToHom (tensorFamily_const X (1 + m))

/-- 概要：先頭を組み込んでから生成射を適用することは各生成射を先に適用することと一致する（Berger–Moerdijk §1）。
方針：生成射を因子ごとの射で表し、先頭の組み込みの自然性を使う。
規約：先頭の生成射と尾の有限テンソル生成射を独立に適用する。
使われ方：二段の Schur 作用の入力の生成射を比較する。 -/
lemma tensorFamilyGenerator_headAssembly {ι : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (m : ℕ) (s : Fin (1 + m) → ι) :
    tensorFamilyHeadAssembly m (fun j => D (s j)) ≫ tensorFamilyGenerator X D e (1 + m) s =
      (e (s ((0 : Fin 1).castAdd m)) ⊗ₘ
        tensorFamilyGenerator X D e m (fun j => s (j.natAdd 1))) ≫
        tensorFamilyHeadAssemblyToPower X m := by
  simp only [tensorFamilyGenerator_asMap, tensorFamilyHeadAssemblyToPower]
  rw [tensorHom_comp_whiskerLeft_assoc]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [← reassoc_of% (tensorFamilyHeadAssembly_naturality m (fun j => e (s j)))]

end SerrePositivity.EInfinity
