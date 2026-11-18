module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnitEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitPowers
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
# 単位対象からの内部 Hom の評価

概要：Berger–Fresse §3.1 の単位余代数からの convolution を元の代数と比較する。
方針：閉構造の標準単位同型を右 tensor 評価で表し、反復評価へ拡張する。
規約：既存の MonoidalClosed.unitIsoSelf と同じ比較射を用いる。
使われ方：区間の端点・定数の底の射と代数としての比較を一致させる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

private lemma closed_unit_evaluation {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [MonoidalClosed K] (B : K) :
    (MonoidalClosed.unitIsoSelf (X := B)).hom =
      (λ_ ((ihom (𝟙_ K)).obj B)).inv ≫ (ihom.ev (𝟙_ K)).app B := by
  exact conjugateEquiv_adjunction_id (ihom.adjunction (𝟙_ K)) (leftUnitorNatIso K).inv B

private lemma unit_pair {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] (X Y : K) {U : K} (u : U ⟶ 𝟙_ K) :
    tensorμ X Y (𝟙_ K) U ≫ ((ρ_ X).hom ⊗ₘ ((Y ◁ u) ≫ (ρ_ Y).hom)) =
      ((X ⊗ Y) ◁ (((𝟙_ K) ◁ u) ≫ (λ_ (𝟙_ K)).hom)) ≫ (ρ_ (X ⊗ Y)).hom := by
  have h : tensorμ X Y (𝟙_ K) (𝟙_ K) ≫ ((ρ_ X).hom ⊗ₘ (ρ_ Y).hom) =
      ((X ⊗ Y) ◁ (λ_ (𝟙_ K)).hom) ≫ (ρ_ (X ⊗ Y)).hom := by
    simp only [tensorμ, braiding_tensorUnit_right, comp_whiskerRight,
      whiskerLeft_comp, Category.assoc]
    monoidal
  have hn := tensorμ_natural_right X Y (𝟙 (𝟙_ K)) u
  simp only [whiskerLeft_id, id_tensorHom] at hn
  rw [← whiskerLeft_comp_tensorHom, ← reassoc_of% hn, h]
  simp only [← whiskerLeft_comp_assoc]

private lemma unit_pair_map {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {X Y B D U : K} (f : X ⟶ B) (g : Y ⟶ D) (u : U ⟶ 𝟙_ K) :
    tensorμ X Y (𝟙_ K) U ≫ (((ρ_ X).hom ≫ f) ⊗ₘ ((g ⊗ₘ u) ≫ (ρ_ D).hom)) =
      ((f ⊗ₘ g) ⊗ₘ (((𝟙_ K) ◁ u) ≫ (λ_ (𝟙_ K)).hom)) ≫ (ρ_ (B ⊗ D)).hom := by
  calc
    _ = tensorμ X Y (𝟙_ K) U ≫
        ((ρ_ X).hom ⊗ₘ ((Y ◁ u) ≫ (ρ_ Y).hom)) ≫ (f ⊗ₘ g) := by
      rw [tensorHom_comp_tensorHom]
      simp only [tensorHom_def' g u, Category.assoc, rightUnitor_naturality]
    _ = _ := by
      rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.unit_pair X Y u), tensorHom_def' (f ⊗ₘ g),
        Category.assoc, rightUnitor_naturality]

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：単位からの内部 Hom の評価は標準単位同型の評価となる（BF §3.1）。
方針：左 tensor の評価を braiding によって右評価へ移す。
規約：比較射は MonoidalClosed.unitIsoSelf の順方向。
使われ方：単位余代数からの反復評価を単位冪の縮約へ帰着する。 -/
lemma convolutionEvaluation_unit_source (B : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation (𝟙_ (Complex A)) B =
    (ρ_ (homComplex A (𝟙_ (Complex A)) B)).hom ≫
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom := by
  have he : (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom =
      (λ_ (homComplex A (𝟙_ (Complex A)) B)).inv ≫
        (ihom.ev (𝟙_ (Complex A))).app B := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.closed_unit_evaluation B
  have hv : (ihom.ev (𝟙_ (Complex A))).app B =
      (β_ (𝟙_ (Complex A)) (homComplex A (𝟙_ (Complex A)) B)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation (𝟙_ (Complex A)) B := by
    rw [← evaluation_eq, _root_.SerrePositivity.DifferentialGraded.evaluation, tensorHomEquiv_uncurryRight]
    rfl
  rw [hv, braiding_tensorUnit_left] at he
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at he
  rw [he]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 概要：単位始域の転置を標準単位同型で評価する（BF §3.1）。
方針：評価による逆転置を右単位子の自然性で移す。
規約：任意の複体の射を扱う。
使われ方：単位余代数の convolution の評価公式を代数射の保存則へ戻す。 -/
lemma curryRight_unit_source_evaluation {Q B : Complex A}
    (f : Q ⊗ (𝟙_ (Complex A)) ⟶ B) :
    curryRight f ≫ (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom =
      (ρ_ Q).inv ≫ f := by
  have hu := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_uncurry (curryRight f)
  simp only [uncurryRight_curryRight, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_unit_source,
    rightUnitor_naturality_assoc] at hu
  calc
    _ = (ρ_ Q).inv ≫ (ρ_ Q).hom ≫ curryRight f ≫
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom := by
      rw [Iso.inv_hom_id_assoc]
    _ = _ := congrArg (fun z => (ρ_ Q).inv ≫ z) hu.symm

/-- 概要：単位始域の反復評価は各関数の単位評価と単位冪の縮約（BF §3.1）。
方針：一因子の評価公式をテンソル分離の単位子との整合性で反復する。
規約：零入力の評価も含む。
使われ方：単位余代数からの convolution 演算を元の代数の演算と比較する。 -/
lemma convolutionPowerEvaluation_unit_source (B : Complex A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation (𝟙_ (Complex A)) B n =
    (_root_.SerrePositivity.TensorPowers.map (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom n ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).hom) ≫ (ρ_ (power B n)).hom := by
  induction n with
  | zero =>
    change (λ_ (𝟙_ (Complex A))).hom =
      (𝟙 (𝟙_ (Complex A)) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ (ρ_ (𝟙_ (Complex A))).hom
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, unitors_equal]
  | succ n ih =>
    change tensorμ (homComplex A (𝟙_ (Complex A)) B)
        (power (homComplex A (𝟙_ (Complex A)) B) n) (𝟙_ (Complex A))
        (power (𝟙_ (Complex A)) n) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation (𝟙_ (Complex A)) B ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation (𝟙_ (Complex A)) B n) =
      (((MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom ⊗ₘ
          _root_.SerrePositivity.TensorPowers.map (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B)).hom n) ⊗ₘ
        (((𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).hom) ≫
          (λ_ (𝟙_ (Complex A))).hom)) ≫ (ρ_ (B ⊗ power B n)).hom
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_unit_source, ih]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.unit_pair_map _ _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
