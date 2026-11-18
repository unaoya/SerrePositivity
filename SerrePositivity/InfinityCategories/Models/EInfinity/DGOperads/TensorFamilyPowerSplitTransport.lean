module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorMap

/-!
模型。文献の定義との比較は後で
# 有限テンソル族のブロック分離をテンソル冪へ移す

概要：Berger–Moerdijk §1 の部分合成の入力を、一般の対象のテンソル冪で二ブロックへ分離する。
方針：一定族とテンソル冪の同一視を有限族の分離同型の前後へ合成する。
規約：空のブロックを含み、各ブロック内の順序を保つ。
使われ方：生成射上の部分合成則を一般の入力テンソル冪へ拡張する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：テンソル冪を前半と後半のテンソル冪へ分離する同型（Berger–Moerdijk §1）。
方針：一定の有限テンソル族へ移し、二ブロック分離の後で両ブロックをテンソル冪へ戻す。
規約：長さは n+m から n,m へ分ける。
使われ方：内側の演算が受け取る入力と外側に残る入力を分離する。 -/
def tensorFamilyPowerSplitIso (X : Complex A) (n m : ℕ) :
    power X (n + m) ≅ power X n ⊗ power X m :=
  (eqToIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const X (n + m))).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun _ => X) ≪≫
    tensorIso (eqToIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const X n)) (eqToIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const X m))

/-- 概要：有限族の生成射はテンソル冪の二ブロック分離と両立する（Berger–Moerdijk §1）。
方針：生成射を因子ごとの射で表し、分離の自然性と一定族の同一視を使う。
規約：二つのブロックの生成射を独立にテンソルする。
使われ方：一般の入力のブロック分離を Schur 生成射上で計算する。 -/
lemma tensorFamilyGenerator_splitToPower {ι : Type} (X : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (n m : ℕ) (s : Fin (n + m) → ι) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e (n + m) s ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso X n m).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => D (s j))).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e n (fun j => s (j.castAdd m)) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X D e m (fun j => s (j.natAdd n))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator_asMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPowerSplitIso, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv, tensorIso_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt_naturality n m (fun j => e (s j)))]
  simp only [tensorHom_comp_tensorHom]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
