module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockTensorAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorCoefficientSeparation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorSplitAt

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：前半の入力族を一因子へまとめ、後半とともに外側の入力族へ送る（Berger–Moerdijk §1）。
方針：二ブロック分離、前半への射 f、先頭の再結合を順に適用する。
規約：f は前半の arity の和で添字付けた複体へ送る。
使われ方：内側の全合成の入力を連結して外側の入力へ送る。 -/
def firstBlockFamilyCollapse (D : ℕ → Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => D (s j)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => D (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => D (s j))).hom ≫
    (f ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd n)))) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly D n m s

/-- 概要：係数 C と前半の入力族を一演算へまとめて外側の入力族へ送る（Berger–Moerdijk §1）。
方針：二ブロック分離の後で係数を前半に合わせ、合成射 f と先頭の再結合を適用する。
規約：後半には恒等射を作用させる。
使われ方：先頭の内側演算を外側の全合成の入力へ渡す。 -/
def firstBlockFamilySubstitution (C : Complex A) (D : ℕ → Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m))) :
    C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => D (s j)) ⟶
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (1 + m) (fun j => D (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j)) :=
  (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => D (s j))).hom) ≫
    (α_ C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s (j.castAdd m))))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd n))))).inv ≫
    (f ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => D (s (j.natAdd n)))) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly D n m s

/-- 概要：先頭の代入を係数族と入力族の独立な代入へ分離できる（Berger–Moerdijk §1）。
方針：二ブロック分離と先頭の再結合をテンソル分離へ通し、係数を含む分離の整合性を使う。
規約：f は係数を含む合成、g は入力族をまとめる射。
使われ方：Schur 演算の二段の合成を係数の結合則と入力の連結則へ帰着する。 -/
lemma firstBlockFamilySubstitution_tensor (C : Complex A) (D E : ℕ → Complex A)
    (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : C ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m)))
    (g : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => E (s (j.castAdd m))) ⟶ E (∑ j : Fin n, s (j.castAdd m))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilySubstitution C (fun r => D r ⊗ E r) n m s
      ((C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => D (s (j.castAdd m)))
        (fun j => E (s (j.castAdd m)))).hom) ≫
      (α_ C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => D (s (j.castAdd m))))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => E (s (j.castAdd m))))).inv ≫ (f ⊗ₘ g)) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (1 + m) (fun j => D (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j))
        (fun j => E (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s j))).hom =
    (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + m) (fun j => D (s j)) (fun j => E (s j))).hom) ≫
      (α_ C (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => D (s j)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + m) (fun j => E (s j)))).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilySubstitution C D n m s f ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyCollapse E n m s g) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilySubstitution _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyCollapse
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly_tensor]
  erw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoefficientSeparation_maps
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => D (s (j.castAdd m))) (fun j => E (s (j.castAdd m)))).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso m (fun j => D (s (j.natAdd n))) (fun j => E (s (j.natAdd n)))).hom f g)]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_splitAt]
  simp only [whiskerLeft_comp, Category.assoc]
  have ha := associator_inv_naturality (𝟙 C)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => D (s j))).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => E (s j))).hom
  simp only [id_tensorHom] at ha
  erw [reassoc_of% ha]
  simp only [tensorHom_comp_tensorHom, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
