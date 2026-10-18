module

public import SerrePositivity.EInfinity.Operad.TensorFamilyPowerSplitTransport

/-!
# 有限族の分離から得られる先頭入力への作用

概要：Berger–Moerdijk §1 の先頭への部分合成の入力射を一般の対象のテンソル冪上で構成する。
方針：入力を前半と後半へ分離し、前半へ指定の演算を適用して再結合する。
規約：外側の入力数を 1+m と表し、先頭の演算の入力数 n は零でもよい。
使われ方：Schur 生成射上の先頭の作用の式を一般の入力へ拡張する。
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

/-- 概要：前半の n 入力へ演算を適用して先頭へ置き、後半 m 入力を保つ射（Berger–Moerdijk §1）。
方針：有限族から移送したテンソル冪の分離同型と先頭の組み込みを使う。
規約：出力の入力数は 1+m。
使われ方：先頭での Schur 作用の結合則を一般のテンソル冪で表す。 -/
def firstSlotPowerAction (X C : Complex A) (n m : ℕ) (θ : C ⊗ power X n ⟶ X) :
    C ⊗ power X (n + m) ⟶ power X (1 + m) :=
  (C ◁ (tensorFamilyPowerSplitIso X n m).hom) ≫
    (α_ C (power X n) (power X m)).inv ≫ (θ ▷ power X m) ≫
    tensorFamilyHeadAssemblyToPower X m

/-- 概要：先頭への作用は入力の生成射上で前半の演算と後半の生成射を独立に適用する（Berger–Moerdijk §1）。
方針：入力生成射とテンソル冪の分離の両立、結合子の自然性を使う。
規約：θ は一般の対象 X 上の n 入力の射。
使われ方：Schur 作用の先頭での部分合成則を生成射上で検証する。 -/
lemma firstSlotPowerAction_generators {ι : Type} (X C : Complex A) (D : ι → Complex A)
    (e : ∀ i, D i ⟶ X) (n m : ℕ) (θ : C ⊗ power X n ⟶ X) (s : Fin (n + m) → ι) :
    (C ◁ tensorFamilyGenerator X D e (n + m) s) ≫ firstSlotPowerAction X C n m θ =
    (C ◁ (tensorFamilySplitAt n m (fun j => D (s j))).hom) ≫
      (α_ C (tensorFamily n (fun j => D (s (j.castAdd m))))
        (tensorFamily m (fun j => D (s (j.natAdd n))))).inv ≫
      (((C ◁ tensorFamilyGenerator X D e n (fun j => s (j.castAdd m))) ≫ θ) ⊗ₘ
        tensorFamilyGenerator X D e m (fun j => s (j.natAdd n))) ≫
      tensorFamilyHeadAssemblyToPower X m := by
  unfold firstSlotPowerAction
  rw [← whiskerLeft_comp_assoc, tensorFamilyGenerator_splitToPower]
  simp only [whiskerLeft_comp, Category.assoc]
  have hn := associator_inv_naturality (𝟙 C)
    (tensorFamilyGenerator X D e n (fun j => s (j.castAdd m)))
    (tensorFamilyGenerator X D e m (fun j => s (j.natAdd n)))
  simp only [id_tensorHom] at hn
  rw [reassoc_of% hn]
  rw [← tensorHom_id θ, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]

end SerrePositivity.EInfinity
