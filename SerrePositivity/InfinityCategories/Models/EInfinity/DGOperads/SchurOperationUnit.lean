module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# Schur 演算の生成射における単位作用

概要：Berger–Moerdijk §1 の単位演算が Schur 演算の生成射上で恒等に作用することを証明する。
方針：一次の合成の単位則と、係数・入力の分離と連結の単位子の式を組み合わせる。
規約：arity の等式による係数と入力の移送は Schur 生成射で同時に相殺する。
使われ方：Schur 対象の作用射の単位則を生成射上で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

/-- 概要：Schur 生成射は arity の等式による係数と入力の移送を相殺する（Berger–Moerdijk §1）。
方針：arity の等式で長さを同一視し、恒等射を簡約する。
規約：係数と入力のテンソル冪の両方を同じ arity の等式で移す。
使われ方：一次の演算の単位則で総和の arity を元の入力の arity に戻す。 -/
lemma schurι_index_eq (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A)
    {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level P) h) ⊗ₘ
      eqToHom (congrArg (power K) h)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P K m := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Category.id_comp]

@[reassoc]
private lemma coefficient_precompose {C D S V W R Z Y : Complex A}
    (u : D ⟶ C) (v : S ⟶ V ⊗ W) (f : C ⊗ V ⟶ R) (l : W ⟶ Z) (q : R ⊗ Z ⟶ Y) :
    (u ▷ S) ≫ (C ◁ v) ≫ (α_ C V W).inv ≫ (f ⊗ₘ l) ≫ q =
      (D ◁ v) ≫ (α_ D V W).inv ≫ (((u ▷ V) ≫ f) ⊗ₘ l) ≫ q := by
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    whiskerRight_comp_tensorHom_assoc]

@[reassoc]
private lemma lambda_tensor {V W R Z : Complex A} (f : V ⟶ R) (g : W ⟶ Z) :
    (α_ (𝟙_ (Complex A)) V W).inv ≫ (((λ_ V).hom ≫ f) ⊗ₘ g) =
      (λ_ (V ⊗ W)).hom ≫ (f ⊗ₘ g) := by
  have h : (α_ (𝟙_ (Complex A)) V W).inv ≫ ((λ_ V).hom ▷ W) =
      (λ_ (V ⊗ W)).hom := by monoidal_coherence
  rw [← whiskerRight_comp_tensorHom, ← Category.assoc, h]

private lemma one_operation_unit {C S U W R Z Y : Complex A}
    (u : 𝟙_ (Complex A) ⟶ C) (v : S ⟶ (U ⊗ 𝟙_ (Complex A)) ⊗ (W ⊗ 𝟙_ (Complex A)))
    (f : C ⊗ (U ⊗ 𝟙_ (Complex A)) ⟶ R) (l : W ⊗ 𝟙_ (Complex A) ⟶ Z)
    (q : R ⊗ Z ⟶ Y) (a : U ⟶ R) (b : W ⟶ Z) (r : S ⟶ U ⊗ W) (q₀ : U ⊗ W ⟶ Y)
    (hf : (u ▷ (U ⊗ 𝟙_ (Complex A))) ≫ f =
      (λ_ (U ⊗ 𝟙_ (Complex A))).hom ≫ (ρ_ U).hom ≫ a)
    (hl : l = (ρ_ W).hom ≫ b)
    (hv : v ≫ ((ρ_ U).hom ⊗ₘ (ρ_ W).hom) = r) (hq : (a ⊗ₘ b) ≫ q = q₀) :
    (u ▷ S) ≫ (C ◁ v) ≫
      (α_ C (U ⊗ 𝟙_ (Complex A)) (W ⊗ 𝟙_ (Complex A))).inv ≫ (f ⊗ₘ l) ≫ q =
        (λ_ S).hom ≫ r ≫ q₀ := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.coefficient_precompose, hf, hl, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.lambda_tensor_assoc,
    ← tensorHom_comp_tensorHom_assoc, leftUnitor_naturality_assoc]
  rw [← Category.assoc v ((ρ_ U).hom ⊗ₘ (ρ_ W).hom) ((a ⊗ₘ b) ≫ q), hv, hq]

namespace Operad

/-- 概要：単位演算を作用させた Schur 演算の生成射は元の生成射に一致する（Berger–Moerdijk §1）。
方針：一次の合成の左単位則を適用し、分離同型と連結同型の単位子を相殺する。
規約：一要素の内側 arity 族は arity 0 も許す。
使われ方：Schur 対象上の作用射の単位則を導く。 -/
lemma schurOperationGenerator_unit (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (s : Fin 1 → ℕ) :
    (P.unit ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 1 (fun i => P.arity (s i) ⊗ power K (s i))) ≫
      P.schurOperationGenerator K 1 s =
        (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 1 (fun i => P.arity (s i) ⊗ power K (s i)))).hom ≫
          (ρ_ (P.arity (s 0) ⊗ power K (s 0))).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s 0) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.one_operation_unit P.unit
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso 1 (fun i => P.arity (s i)) (fun i => power K (s i))).hom
    (P.composition 1 s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K 1 s).hom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (∑ i, s i))
    (eqToHom (congrArg P.arity (by simp : s 0 = ∑ i, s i)))
    (eqToHom (congrArg (power K) (by simp : s 0 = ∑ i, s i)))
    (ρ_ (P.arity (s 0) ⊗ power K (s 0))).hom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s 0))
    (P.unit_composition_one s) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_one K s)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_one (fun i => P.arity (s i)) (fun i => power K (s i)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_index_eq P.sequence K (by simp : s 0 = ∑ i, s i))

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
