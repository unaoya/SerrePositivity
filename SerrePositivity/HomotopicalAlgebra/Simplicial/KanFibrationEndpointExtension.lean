module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoEndpointExtension

/-!
# Kan fibration上の指定区間を始点と基底の区間を保って延長する

## 概要
Kan fibration上の指定区間を始点と基底の区間を保って延長する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0411][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0411
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Extend a specified interval over its specified base along a Kan fibration

One whole endpoint, the original restricted interval, and the whole base
interval are all retained. The base need not itself be a Kan complex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanFibrationEndpointExtension
variable {A T E B : SSet.{v}} (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (i : A ⟶ T) [Mono i]

include hp in
lemma exists_from_one (b : T ⟶ E) (a : A ⟶ E) (H : SSet.Homotopy a (i ≫ b))
    (q : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ p = SSet.ι₁ ≫ q)
    (hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ ∃ V : SSet.Homotopy g b,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ p = q := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (0 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 0 1 (by decide))
  have : HasLiftingProperty pp.ι p := ha _ hp
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst T _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_one H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst T _ ≫ b) H.h hc
  have hface : (fst T (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ b) ≫ p =
      T ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ q := by
    rw [Category.assoc, hb]
    have he : T ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst T _ ≫ SSet.ι₁ := by
      rw [SSet.stdSimplex.δ_zero_eq_const]
      rfl
    rw [he, Category.assoc]
  have hw : u ≫ p = pp.ι ≫ q := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc,
        ← Category.assoc, pp.inl_ι]
      exact hface
    · rw [← Category.assoc, pp.isPushout.inr_desc,
        ← Category.assoc, pp.inr_ι]
      exact hH
  let sq : CommSq u pp.ι p q := ⟨hw⟩
  have ho : T ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ sq.lift = fst T _ ≫ b := by
    rw [show T ◁ SSet.stdSimplex.δ (0 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hr : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  let g := SSet.ι₀ ≫ sq.lift
  have hg : i ≫ g = a := by
    dsimp only [g]
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hr]
    exact H.h₀
  refine ⟨g, hg, { h := sq.lift, h₀ := rfl, h₁ := ?_, rel := ?_ }, hr, sq.fac_right⟩
  · change SSet.ι₁ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_one T, Category.assoc, ho]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)


include hp in
/-- Kan fibration上の指定区間を始点と基底の区間を保って延長する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
指定された境界と基底から可換正方形を作り、その持ち上げ性を使う。
元の指定部分を保つ等式は、対角射の二つの分解等式から確認する。
-/
lemma exists_from_zero (b : T ⟶ E) (a : A ⟶ E) (H : SSet.Homotopy (i ≫ b) a)
    (q : T ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ p = SSet.ι₀ ≫ q)
    (hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ ∃ V : SSet.Homotopy b g,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ p = q := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.stdSimplex.δ (1 : Fin 2))
  have ha : SSet.anodyneExtensions pp.ι :=
    SSet.anodyneExtensions_pushoutObjObjι pp (AnodyneHomotopy.delta_anodyne 1 0 (by decide))
  have : HasLiftingProperty pp.ι p := ha _ hp
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 0) ≫ (fst T _ ≫ b) =
      A ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h := by
    rw [HomotopyEndpointComparison.face_zero H]
    exact whiskerRight_fst_assoc i _ b
  let u := pp.isPushout.desc (fst T _ ≫ b) H.h hc
  have hface : (fst T (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≫ b) ≫ p =
      T ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ q := by
    rw [Category.assoc, hb]
    have he : T ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst T _ ≫ SSet.ι₀ := by
      rw [SSet.stdSimplex.δ_one_eq_const]
      rfl
    rw [he, Category.assoc]
  have hw : u ≫ p = pp.ι ≫ q := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc,
        ← Category.assoc, pp.inl_ι]
      exact hface
    · rw [← Category.assoc, pp.isPushout.inr_desc,
        ← Category.assoc, pp.inr_ι]
      exact hH
  let sq : CommSq u pp.ι p q := ⟨hw⟩
  have ho : T ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ sq.lift = fst T _ ≫ b := by
    rw [show T ◁ SSet.stdSimplex.δ (1 : Fin 2) = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hr : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ sq.lift = H.h := by
    rw [show i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) = pp.inr ≫ pp.ι from
      pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  let g := SSet.ι₁ ≫ sq.lift
  have hg : i ≫ g = a := by
    dsimp only [g]
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hr]
    exact H.h₁
  refine ⟨g, hg, { h := sq.lift, h₀ := ?_, h₁ := rfl, rel := ?_ }, hr, sq.fac_right⟩
  · change SSet.ι₀ ≫ sq.lift = b
    rw [← LargeParameterHomotopy.section_zero T, Category.assoc, ho]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.KanFibrationEndpointExtension
