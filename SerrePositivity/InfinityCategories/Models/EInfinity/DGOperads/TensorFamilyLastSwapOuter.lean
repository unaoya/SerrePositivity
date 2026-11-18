module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyLastSwapCompatibility

/-!
模型。文献の定義との比較は後で
# 外側の係数射を伴う末尾交換と分離

概要：Berger–Moerdijk §1 の反復合成で、外側の係数射と末尾二因子の交換を分離同型に通す。
方針：有限テンソル族の末尾交換の可換性にテンソル積の合成則を適用する。
規約：外側の係数射は任意の自己射とし、前半の因子は固定する。
使われ方：外側の入力交換と分離された二因子への対称性を結び付ける。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：外側の係数射と末尾交換は分離後の係数射と末尾二因子の対称性に一致する（Berger–Moerdijk §1）。
方針：テンソル積の合成則で入力族の射をまとめ、末尾交換と分離の可換性を適用する。
規約：前半の有限テンソルに作用する射は恒等。
使われ方：末尾二入力の外側等変性を分離された二位置への合成に適用する。 -/
@[reassoc]
lemma tensorFamilySplitLastTwo_lastSwap_outer (n : ℕ) (V : Fin (n + 2) → Complex A)
    {R : Complex A} (a : R ⟶ R) :
    (a ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) V (Fin.last n)).hom) ≫
        (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n
          (fun i => V (adjacentTransposition (Fin.last n) i))).hom) ≫
        (R ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_lastSwap_output_obj n V)) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo n V).hom) ≫
        (a ⊗ₘ (𝟙 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.castSucc)) ⊗ₘ
          (β_ (V (Fin.last n).castSucc) (V (Fin.last (n + 1)))).hom)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLastTwo_lastSwap n V
  simp only [← id_tensorHom] at h
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [h]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
