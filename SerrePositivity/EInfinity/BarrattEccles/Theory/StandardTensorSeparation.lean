module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryEvaluation
public import SerrePositivity.EInfinity.Operad.TensorFamilyUnitSeparation

/-!
# 標準入力のテンソル冪と単位入力の分離

HA 3.2.4.7 の指定 Hopf 比較の計算。BS-W16 の型一覧 L10〜L12 と追加照合 I2。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local implicit_reducible] tensorFamily TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {R : Type u} [CommRing R]

/-- 一定族の二列分離は、指定されたテンソル冪の分離と一致する。 -/
lemma tensorFamilyTensorIso_const (K L : Complex R) (r : ℕ) :
    eqToHom (tensorFamily_const (K ⊗ L) r) ≫ (tensorPowerSeparation K L r).hom =
    (tensorFamilyTensorIso r (fun _ => K) (fun _ => L)).hom ≫
      (eqToHom (tensorFamily_const K r) ⊗ₘ eqToHom (tensorFamily_const L r)) := by
  induction r with
  | zero =>
    change 𝟙 _ ≫ (λ_ (𝟙_ (Complex R))).inv =
      (λ_ (𝟙_ (Complex R))).inv ≫ (𝟙 _ ⊗ₘ 𝟙 _)
    simp only [Category.id_comp, tensorHom_id, id_whiskerRight, Category.comp_id]
  | succ r ih =>
    simp only [tensorFamily_const_succ_hom, tensorPowerSeparation,
      tensorFamilyTensorIso, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
    rw [← whiskerLeft_comp_assoc, ih, whiskerLeft_comp, Category.assoc]
    rw [tensorμ_natural_right]

/-- 左単位を因子ごとに挿入して分離すると、単位族の逆を挿入する射になる。 -/
lemma tensorFamilyTensorIso_insert_left (r : ℕ) (V : Fin r → Complex R) :
    tensorFamilyMap r (fun j => (λ_ (V j)).inv) ≫
      (tensorFamilyTensorIso r (fun _ => 𝟙_ (Complex R)) V).hom =
    (λ_ (tensorFamily r V)).inv ≫
      ((tensorUnitFamilyIso R r).inv ⊗ₘ 𝟙 (tensorFamily r V)) := by
  apply (cancel_mono (((tensorUnitFamilyIso R r).hom ⊗ₘ 𝟙 (tensorFamily r V)) ≫
    (λ_ (tensorFamily r V)).hom)).1
  simp only [Category.assoc]
  rw [tensorFamilyTensorIso_unit_left, ← tensorFamilyMap_comp]
  simp only [Iso.inv_hom_id, tensorFamilyMap_id, tensorHom_id]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id]

/-- 右の単位入力を含むテンソル冪は、同じ指定単位族へ分離される。 -/
lemma tensorPowerSeparation_insert_right {Z K L : Complex R}
    (f : Z ⟶ K) (u : 𝟙_ (Complex R) ⟶ L) (r : ℕ) :
    TensorPowers.map ((ρ_ Z).inv ≫ (f ⊗ₘ u)) r ≫ (tensorPowerSeparation K L r).hom =
    (ρ_ (power Z r)).inv ≫ (TensorPowers.map f r ⊗ₘ
      ((tensorUnitFamilyIso R r).inv ≫ tensorFamilyMap r (fun _ => u) ≫
        eqToHom (tensorFamily_const L r))) := by
  have hc := tensorFamilyGenerator_constant (K ⊗ L) (fun _ : Unit => Z)
    (fun _ => (ρ_ Z).inv ≫ (f ⊗ₘ u)) () r
  have hf := tensorFamilyGenerator_constant K (fun _ : Unit => Z) (fun _ => f) () r
  rw [tensorFamilyGenerator_asMap] at hc hf
  apply (cancel_epi (eqToHom (tensorFamily_const Z r))).1
  rw [← reassoc_of% hc, tensorFamilyTensorIso_const]
  rw [tensorFamilyMap_comp, Category.assoc,
    reassoc_of% tensorFamilyTensorIso_naturality,
    reassoc_of% tensorFamilyTensorIso_insert_right]
  simp only [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hf, rightUnitor_inv_naturality_assoc, whiskerRight_comp_tensorHom]

/-- 左の単位入力を含むテンソル冪は、同じ指定単位族へ分離される。 -/
lemma tensorPowerSeparation_insert_left {Z K L : Complex R}
    (u : 𝟙_ (Complex R) ⟶ K) (f : Z ⟶ L) (r : ℕ) :
    TensorPowers.map ((λ_ Z).inv ≫ (u ⊗ₘ f)) r ≫ (tensorPowerSeparation K L r).hom =
    (λ_ (power Z r)).inv ≫ (((tensorUnitFamilyIso R r).inv ≫ tensorFamilyMap r (fun _ => u) ≫
      eqToHom (tensorFamily_const K r)) ⊗ₘ TensorPowers.map f r) := by
  have hc := tensorFamilyGenerator_constant (K ⊗ L) (fun _ : Unit => Z)
    (fun _ => (λ_ Z).inv ≫ (u ⊗ₘ f)) () r
  have hf := tensorFamilyGenerator_constant L (fun _ : Unit => Z) (fun _ => f) () r
  rw [tensorFamilyGenerator_asMap] at hc hf
  apply (cancel_epi (eqToHom (tensorFamily_const Z r))).1
  rw [← reassoc_of% hc, tensorFamilyTensorIso_const]
  rw [tensorFamilyMap_comp, Category.assoc,
    reassoc_of% tensorFamilyTensorIso_naturality,
    reassoc_of% tensorFamilyTensorIso_insert_left]
  simp only [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hf, leftUnitor_inv_naturality_assoc, whiskerLeft_comp_tensorHom]

/-- 長さを別の式で書いた全単射でも、代数の指定作用は同じ等変性を満たす。 -/
lemma algebra_action_bijection {P : Operad R} (Z : P.Algebra)
    {m n : ℕ} (e : Fin m ≃ Fin n) :
    (P.arityBijectionMap e ⊗ₘ tensorPowerEquivMap Z.carrier e) ≫ Z.action n = Z.action m := by
  have hn : m = n := by simpa using Fintype.card_congr e
  subst n
  rw [tensorPowerEquivMap_perm]
  exact Z.equivariance m e

end SerrePositivity.EInfinity
