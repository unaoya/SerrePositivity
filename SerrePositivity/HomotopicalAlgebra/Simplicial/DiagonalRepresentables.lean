module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalAdjunction
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 対角の右随伴の各値を制限された表現可能関手からの写像として表す

## 概要
対角の右随伴の各値を制限された表現可能関手からの写像として表す。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
積添字の表現可能関手の対角制限を標準単体の積と同定する。
Coyonedaと右Kan拡張の随伴で、右随伴の各単体を計算する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0389][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0389
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Restricted representables and the values of the diagonal right adjoint

Restriction of a representable from the square of Delta-op is the actual
product of two standard simplices. Coyoneda and the constructed right Kan
adjunction then compute each simplex of the actual diagonal right adjoint.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.BisimplicialModel

abbrev pairRepresentable (n m : SimplexCategory) :
    (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v :=
  uliftCoyoneda.{v}.obj (Opposite.op (Opposite.op n, Opposite.op m))

abbrev restrictedRepresentable (n m : SimplexCategory) : SSet.{v} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ pairRepresentable n m

/-- The ULift of a pair of simplex maps is the pair of their ULifts. -/
def restrictedRepresentableIso (n m : SimplexCategory) :
    restrictedRepresentable.{v} n m ≅ SSet.stdSimplex.obj n ⊗ SSet.stdSimplex.obj m :=
  NatIso.ofComponents (fun k => Equiv.toIso {
    toFun := fun x => (ULift.up x.down.1.unop, ULift.up x.down.2.unop)
    invFun := fun x => ULift.up (x.1.down.op, x.2.down.op)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }) (by
      intro k l f
      ext x
      rfl)

/- 旧宣言の技術注記：
Compute a simplex of the actual right adjoint by an ordinary Hom set.
-/
/-- 対角の右随伴の各値を制限された表現可能関手からの写像として表す。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
積添字の表現可能関手の対角制限を標準単体の積と同定する。
Coyonedaと右Kan拡張の随伴で、右随伴の各単体を計算する。
-/
def rightAdjointValueEquiv (Z : SSet.{v}) (n m : SimplexCategory) :
    ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m) ≃
      (SSet.stdSimplex.obj n ⊗ SSet.stdSimplex.obj m ⟶ Z) :=
  uliftCoyonedaEquiv.symm.trans
    (((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v)).homEquiv
      (pairRepresentable n m) Z).symm |>.trans
        (Iso.homCongr (restrictedRepresentableIso n m) (Iso.refl Z))

lemma rightAdjointValueEquiv_formula (Z : SSet.{v}) (n m : SimplexCategory)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    rightAdjointValueEquiv Z n m x = (restrictedRepresentableIso n m).inv ≫
      (((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v)).homEquiv
        (pairRepresentable n m) Z).symm (uliftCoyonedaEquiv.symm x) := by
  simp only [rightAdjointValueEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  rfl

/-- The Hom-set description is natural in the target simplicial set. -/
lemma rightAdjointValueEquiv_target {Z Z' : SSet.{v}} (h : Z ⟶ Z')
    (n m : SimplexCategory)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    rightAdjointValueEquiv Z' n m (((rightAdjoint.map h).app (Opposite.op n)).app
      (Opposite.op m) x) = rightAdjointValueEquiv Z n m x ≫ h := by
  let R : SSet.{v} ⥤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v :=
    (Functor.diag SimplexCategoryᵒᵖ).ran
  let t : pairRepresentable n m ⟶ R.obj Z := uliftCoyonedaEquiv.symm x
  have ht : uliftCoyonedaEquiv.symm ((R.map h).app (Opposite.op n, Opposite.op m) x) =
      t ≫ R.map h := by
    apply uliftCoyonedaEquiv.injective
    have hh := uliftCoyonedaEquiv_comp
      (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) t (R.map h)
    simpa only [t, Equiv.apply_symm_apply] using hh.symm
  rw [rightAdjointValueEquiv_formula, rightAdjointValueEquiv_formula]
  change (restrictedRepresentableIso n m).inv ≫
      (((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v)).homEquiv
        (pairRepresentable n m) Z').symm
        (uliftCoyonedaEquiv.symm ((R.map h).app (Opposite.op n, Opposite.op m) x)) = _
  rw [ht, Adjunction.homEquiv_naturality_right_symm, Category.assoc]

abbrev pairRepresentableMap (n : SimplexCategory) {m' m : SimplexCategory} (g : m' ⟶ m) :
    pairRepresentable.{v} n m' ⟶ pairRepresentable n m :=
  uliftCoyoneda.map (Quiver.Hom.op
    ((𝟙 (Opposite.op n), g.op) :
      (Opposite.op n, Opposite.op m) ⟶ (Opposite.op n, Opposite.op m')))

lemma restrictedRepresentableIso_inner (n : SimplexCategory) {m' m : SimplexCategory}
    (g : m' ⟶ m) :
    (restrictedRepresentableIso.{v} n m').inv ≫
      Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (pairRepresentableMap n g) =
        (SSet.stdSimplex.obj n ◁ SSet.stdSimplex.map g) ≫
          (restrictedRepresentableIso n m).inv := by
  ext k x
  change ULift.up (𝟙 (Opposite.op n) ≫ x.1.down.op, g.op ≫ x.2.down.op) =
    ULift.up (x.1.down.op, (x.2.down ≫ g).op)
  simp only [Category.id_comp, op_comp]

/-- The Hom-set description commutes with inner simplex operators. -/
lemma rightAdjointValueEquiv_inner (Z : SSet.{v}) (n : SimplexCategory)
    {m' m : SimplexCategory} (g : m' ⟶ m)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    rightAdjointValueEquiv Z n m' (((rightAdjoint.obj Z).obj (Opposite.op n)).map g.op x) =
      (SSet.stdSimplex.obj n ◁ SSet.stdSimplex.map g) ≫ rightAdjointValueEquiv Z n m x := by
  let R : SSet.{v} ⥤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v :=
    (Functor.diag SimplexCategoryᵒᵖ).ran
  let t : pairRepresentable n m ⟶ R.obj Z := uliftCoyonedaEquiv.symm x
  have ht : uliftCoyonedaEquiv.symm ((R.obj Z).map (𝟙 (Opposite.op n), g.op) x) =
      pairRepresentableMap n g ≫ t :=
    uliftCoyonedaEquiv_symm_map (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
      (F := R.obj Z) ((𝟙 (Opposite.op n), g.op) :
        (Opposite.op n, Opposite.op m) ⟶ (Opposite.op n, Opposite.op m')) x
  rw [rightAdjointValueEquiv_formula, rightAdjointValueEquiv_formula]
  change (restrictedRepresentableIso n m').inv ≫
      (((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v)).homEquiv
        (pairRepresentable n m') Z).symm
        (uliftCoyonedaEquiv.symm ((R.obj Z).map (𝟙 (Opposite.op n), g.op) x)) = _
  rw [ht, Adjunction.homEquiv_naturality_left_symm]
  change (restrictedRepresentableIso n m').inv ≫
      (Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (pairRepresentableMap n g) ≫
        _) = _
  rw [← Category.assoc, restrictedRepresentableIso_inner, Category.assoc]

abbrev pairRepresentableOuterMap {n' n : SimplexCategory} (g : n' ⟶ n) (m : SimplexCategory) :
    pairRepresentable.{v} n' m ⟶ pairRepresentable n m :=
  uliftCoyoneda.map (Quiver.Hom.op
    ((g.op, 𝟙 (Opposite.op m)) :
      (Opposite.op n, Opposite.op m) ⟶ (Opposite.op n', Opposite.op m)))

lemma restrictedRepresentableIso_outer {n' n : SimplexCategory} (g : n' ⟶ n)
    (m : SimplexCategory) :
    (restrictedRepresentableIso.{v} n' m).inv ≫
      Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (pairRepresentableOuterMap g m) =
        (SSet.stdSimplex.map g ▷ SSet.stdSimplex.obj m) ≫
          (restrictedRepresentableIso n m).inv := by
  ext k x
  change ULift.up (g.op ≫ x.1.down.op, 𝟙 (Opposite.op m) ≫ x.2.down.op) =
    ULift.up ((x.1.down ≫ g).op, x.2.down.op)
  simp only [Category.id_comp, op_comp]

/-- The same concrete description commutes with outer simplex operators. -/
lemma rightAdjointValueEquiv_outer (Z : SSet.{v}) {n' n : SimplexCategory}
    (g : n' ⟶ n) (m : SimplexCategory)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    rightAdjointValueEquiv Z n' m (((rightAdjoint.obj Z).map g.op).app (Opposite.op m) x) =
      (SSet.stdSimplex.map g ▷ SSet.stdSimplex.obj m) ≫ rightAdjointValueEquiv Z n m x := by
  let R : SSet.{v} ⥤ (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type v :=
    (Functor.diag SimplexCategoryᵒᵖ).ran
  let t : pairRepresentable n m ⟶ R.obj Z := uliftCoyonedaEquiv.symm x
  have ht : uliftCoyonedaEquiv.symm ((R.obj Z).map (g.op, 𝟙 (Opposite.op m)) x) =
      pairRepresentableOuterMap g m ≫ t :=
    uliftCoyonedaEquiv_symm_map (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
      (F := R.obj Z) ((g.op, 𝟙 (Opposite.op m)) :
        (Opposite.op n, Opposite.op m) ⟶ (Opposite.op n', Opposite.op m)) x
  rw [rightAdjointValueEquiv_formula, rightAdjointValueEquiv_formula]
  change (restrictedRepresentableIso n' m).inv ≫
      (((Functor.diag SimplexCategoryᵒᵖ).ranAdjunction (Type v)).homEquiv
        (pairRepresentable n' m) Z).symm
        (uliftCoyonedaEquiv.symm ((R.obj Z).map (g.op, 𝟙 (Opposite.op m)) x)) = _
  rw [ht, Adjunction.homEquiv_naturality_left_symm]
  change (restrictedRepresentableIso n' m).inv ≫
      (Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (pairRepresentableOuterMap g m) ≫
        _) = _
  rw [← Category.assoc, restrictedRepresentableIso_outer, Category.assoc]

end SerrePositivity.BisimplicialModel
