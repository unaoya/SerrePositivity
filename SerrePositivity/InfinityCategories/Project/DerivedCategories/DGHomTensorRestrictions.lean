module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTensorFunctor
/-!
概要：大きい dg 圏の二入力 Hom は、固定入力の実右・左代表関手へ厳密に制限される。
方針：三つの実対象の充満像で、既存の対角双加群の制限計算を照合する。
規約：元の入力の Small 性を仮定しない。使われ方：二変数 Hom の実出力分解比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
/-- 有限実充満像に沿う同じ Hom 写像の制限。 -/
lemma dgHomTensorMap_first_finiteImage (n : ℕ) (f : Fin n → C) (i j k : Fin n) :
    dgTensorFirstHom R Cᵒᵖ C (f k) (op (f i)) (op (f j)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op (f i), f k) (op (f j), f k) =
    (representable R (f k)).map (op (f i)) (op (f j)) := by
  let a : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨i⟩
  let b : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨j⟩
  let c : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨k⟩
  have h := (Bimodule.diagonal R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)).uncurryHom_first c (op a) (op b)
  simp only [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_diagonal, Bimodule.diagonal_rightAt] at h
  exact h
/-- 同じ全 Hom 鎖写像の固定入力制限を厳密に照合する。 -/
lemma dgHomTensorMap_first (q : C) (x y : Cᵒᵖ) :
    dgTensorFirstHom R Cᵒᵖ C q x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (x, q) (y, q) =
      (representable R q).map x y := by
  have h := dgHomTensorMap_first_finiteImage R C 3 ![x.unop, y.unop, q] 0 1 2
  dsimp only [Matrix.cons_val] at h
  exact h
/-- 有限実充満像に沿う同じ Hom 写像の制限。 -/
lemma dgHomTensorMap_second_finiteImage (n : ℕ) (f : Fin n → C) (i j k : Fin n) :
    dgTensorSecondHom R Cᵒᵖ C (op (f i)) (f j) (f k) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op (f i), f j) (op (f i), f k) =
    (leftRepresentable R (f i)).map (f j) (f k) := by
  let a : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨i⟩
  let b : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨j⟩
  let c : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨k⟩
  have h := (Bimodule.diagonal R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)).uncurryHom_second a b c
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_diagonal] at h
  have hm := congr_arg_heq (fun F : LeftModule R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) => F.map b c)
    (Bimodule.diagonal_leftAt R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) a)
  rw [eq_of_heq hm] at h
  exact h
/-- 同じ全 Hom 鎖写像の固定入力制限を厳密に照合する。 -/
lemma dgHomTensorMap_second (p x y : C) :
    dgTensorSecondHom R Cᵒᵖ C (op p) x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op p, x) (op p, y) =
      (leftRepresentable R p).map x y := by
  have h := dgHomTensorMap_second_finiteImage R C 3 ![p, x, y] 0 1 2
  dsimp only [Matrix.cons_val] at h
  exact h
/-- 同じ Hom dg 関手の固定入力制限は、元の代表関手に厳密に一致。 -/
lemma dgHomTensorFunctor_first (q : C) :
    (dgTensorIncludeFirst R Cᵒᵖ C q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorFunctor R C) =
      (representable R q).toFunctor := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgTensorIncludeFirst R Cᵒᵖ C q).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorFunctor R C))
    (G := (representable R q).toFunctor) (fun _ => rfl)
  intro x y
  change (dgTensorFirstHom R Cᵒᵖ C q x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (x, q) (y, q)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact dgHomTensorMap_first R C q x y
/-- 同じ Hom dg 関手の固定入力制限は、元の代表関手に厳密に一致。 -/
lemma dgHomTensorFunctor_second (p : C) :
    (dgTensorIncludeSecond R Cᵒᵖ C (op p)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorFunctor R C) =
      leftRepresentable R p := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgTensorIncludeSecond R Cᵒᵖ C (op p)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorFunctor R C))
    (G := leftRepresentable R p) (fun _ => rfl)
  intro x y
  change (dgTensorSecondHom R Cᵒᵖ C (op p) x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op p, x) (op p, y)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact dgHomTensorMap_second R C p x y
end SerrePositivity.InfinityCategories.Project.DerivedCategories
