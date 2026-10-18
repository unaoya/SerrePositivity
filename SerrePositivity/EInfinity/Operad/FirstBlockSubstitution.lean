module

public import SerrePositivity.EInfinity.Operad.FirstBlockTensorAssembly
public import SerrePositivity.EInfinity.Operad.TensorCoefficientSeparation
public import SerrePositivity.EInfinity.Operad.TensorFamilyTensorSplitAt

/-!
# 先頭ブロックへの代入を二つの複体族へ分離する

概要：Berger–Moerdijk §1 の二段の全合成で、先頭ブロックの係数と入力をまとめる射を比較する。
方針：前半と後半を分離し、前半の合成結果をまとめた arity 族へ組み込む。
規約：先頭ブロックの合成射は任意とし、追加の代数的仮定を課さない。
使われ方：Schur 演算の係数の合成と入力の連結を同じテンソル射へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：前半の入力族を一因子へまとめ、後半とともに外側の入力族へ送る（Berger–Moerdijk §1）。
方針：二ブロック分離、前半への射 f、先頭の再結合を順に適用する。
規約：f は前半の arity の和で添字付けた複体へ送る。
使われ方：内側の全合成の入力を連結して外側の入力へ送る。 -/
def firstBlockFamilyCollapse (D : ℕ → Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m))) :
    tensorFamily (n + m) (fun j => D (s j)) ⟶
      tensorFamily (1 + m) (fun j => D (firstBlockArities n m s j)) :=
  (tensorFamilySplitAt n m (fun j => D (s j))).hom ≫
    (f ▷ tensorFamily m (fun j => D (s (j.natAdd n)))) ≫ firstBlockFamilyAssembly D n m s

/-- 概要：係数 C と前半の入力族を一演算へまとめて外側の入力族へ送る（Berger–Moerdijk §1）。
方針：二ブロック分離の後で係数を前半に合わせ、合成射 f と先頭の再結合を適用する。
規約：後半には恒等射を作用させる。
使われ方：先頭の内側演算を外側の全合成の入力へ渡す。 -/
def firstBlockFamilySubstitution (C : Complex A) (D : ℕ → Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : C ⊗ tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m))) :
    C ⊗ tensorFamily (n + m) (fun j => D (s j)) ⟶
      tensorFamily (1 + m) (fun j => D (firstBlockArities n m s j)) :=
  (C ◁ (tensorFamilySplitAt n m (fun j => D (s j))).hom) ≫
    (α_ C (tensorFamily n (fun j => D (s (j.castAdd m))))
      (tensorFamily m (fun j => D (s (j.natAdd n))))).inv ≫
    (f ▷ tensorFamily m (fun j => D (s (j.natAdd n)))) ≫ firstBlockFamilyAssembly D n m s

/-- 概要：先頭の代入を係数族と入力族の独立な代入へ分離できる（Berger–Moerdijk §1）。
方針：二ブロック分離と先頭の再結合をテンソル分離へ通し、係数を含む分離の整合性を使う。
規約：f は係数を含む合成、g は入力族をまとめる射。
使われ方：Schur 演算の二段の合成を係数の結合則と入力の連結則へ帰着する。 -/
lemma firstBlockFamilySubstitution_tensor (C : Complex A) (D E : ℕ → Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : C ⊗ tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m)))
    (g : tensorFamily n (fun j => E (s (j.castAdd m))) ⟶ E (∑ j : Fin n, s (j.castAdd m))) :
    firstBlockFamilySubstitution C (fun r => D r ⊗ E r) n m s
      ((C ◁ (tensorFamilyTensorIso n (fun j => D (s (j.castAdd m)))
        (fun j => E (s (j.castAdd m)))).hom) ≫
      (α_ C (tensorFamily n (fun j => D (s (j.castAdd m))))
        (tensorFamily n (fun j => E (s (j.castAdd m))))).inv ≫ (f ⊗ₘ g)) ≫
      (tensorFamilyTensorIso (1 + m) (fun j => D (firstBlockArities n m s j))
        (fun j => E (firstBlockArities n m s j))).hom =
    (C ◁ (tensorFamilyTensorIso (n + m) (fun j => D (s j)) (fun j => E (s j))).hom) ≫
      (α_ C (tensorFamily (n + m) (fun j => D (s j)))
        (tensorFamily (n + m) (fun j => E (s j)))).inv ≫
      (firstBlockFamilySubstitution C D n m s f ⊗ₘ firstBlockFamilyCollapse E n m s g) := by
  unfold firstBlockFamilySubstitution firstBlockFamilyCollapse
  simp only [Category.assoc]
  rw [firstBlockFamilyAssembly_tensor]
  erw [reassoc_of% (tensorCoefficientSeparation_maps
    (tensorFamilyTensorIso n (fun j => D (s (j.castAdd m))) (fun j => E (s (j.castAdd m)))).hom
    (tensorFamilyTensorIso m (fun j => D (s (j.natAdd n))) (fun j => E (s (j.natAdd n)))).hom f g)]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [tensorFamilyTensorIso_splitAt]
  simp only [whiskerLeft_comp, Category.assoc]
  have ha := associator_inv_naturality (𝟙 C)
    (tensorFamilySplitAt n m (fun j => D (s j))).hom
    (tensorFamilySplitAt n m (fun j => E (s j))).hom
  simp only [id_tensorHom] at ha
  erw [reassoc_of% ha]
  simp only [tensorHom_comp_tensorHom, Category.assoc]

end SerrePositivity.EInfinity
