module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientRestrictionCoherence
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso

/-!
# 厳密な代数の係数制限の関手性

## 概要
HA §3.2.2 の恒等と合成の比較を、同じ底の複体と作用で構成する。

## 方針
演算とテンソル冪の二つの係数比較の合成を展開する。

## 規約
比較の底の複体射は恒等である。

## 使われ方
導来係数制限の恒等と合成の欄。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
open Functor.LaxMonoidal

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

variable {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
  (f : S →+* T) (g : T →+* W)

local notation "R" => ScalarExtension.restriction

/-- 合成によるテンソル冪の比較は二つの比較の合成。 -/
lemma restrictionPower_comp (X : Complex W) (n : ℕ) :
    laxPowerComparison (R (g.comp f)) X n =
      laxPowerComparison (R f) ((R g).obj X) n ≫ (R f).map (laxPowerComparison (R g) X n) := by
  induction n with
  | zero => exact restrictionUnit_comp f g
  | succ n ih =>
    simp only [laxPowerComparison, power]
    rw [ih, restrictionTensor_comp, MonoidalCategory.whiskerLeft_comp, (R f).map_comp]
    let U := R g
    let V := R f
    let a := V.obj (U.obj X) ◁ laxPowerComparison V (U.obj X) n
    let b := V.map (μ U X (power X n))
    let h := μ_natural_right V (U.obj X) (laxPowerComparison U X n)
    have ht := congrArg (fun k => a ≫ k ≫ b) h
    simp only [Category.assoc] at ht
    exact ht

/-- 厳密係数制限の代数作用は二段階に制限しても同じ。 -/
lemma coefficientRestriction_comp_action (X : (operad W).Algebra) (n : ℕ) :
    ((coefficientRestriction (g.comp f)).obj X).action n =
      ((coefficientRestriction f).obj ((coefficientRestriction g).obj X)).action n := by
  let P (A : Type u) [CommRing A] := (operad A).arity n
  let K := X.carrier
  let p := laxPowerComparison (R f) ((R g).obj K) n
  let q := laxPowerComparison (R g) K n
  let c : P S ⟶ (R f).obj (P T) := coefficientComplexMap f n
  let d : P T ⟶ (R g).obj (P W) := coefficientComplexMap g n
  change (coefficientComplexMap (g.comp f) n ⊗ₘ
      laxPowerComparison (R (g.comp f)) K n) ≫
        μ (R (g.comp f)) (P W) (power K n) ≫ (R f).map ((R g).map (X.action n)) =
    (c ⊗ₘ p) ≫ μ (R f) (P T) (power ((R g).obj K) n) ≫
      (R f).map ((d ⊗ₘ q) ≫ μ (R g) (P W) (power K n) ≫ (R g).map (X.action n))
  rw [coefficientComplexMap_comp, restrictionPower_comp, restrictionTensor_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← tensorHom_comp_tensorHom_assoc]
  let V := R f
  let t := V.map (μ (R g) (P W) (power K n)) ≫ V.map ((R g).map (X.action n))
  exact (by
    simpa only [Category.assoc] using congrArg (fun k => (c ⊗ₘ p) ≫ k ≫ t) (μ_natural V d q))

/-- 恒等関手上の標準比較は、オペラッド代数の作用を変えない。 -/
def operadTransportIdentityIso {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)
    (F : Complex A ⥤ Complex A) [b : F.LaxBraided] (k : Operad.LaxComparison F P P)
    (hF : F = 𝟭 (Complex A))
    (hε : HEq (ε F) (𝟙 (𝟙_ (Complex A))))
    (hμ : ∀ X Y : Complex A, HEq (μ F X Y) (𝟙 (X ⊗ Y)))
    (hc : ∀ n, HEq (k.arity n) (𝟙 (P.arity n))) :
    Operad.transport k ≅ 𝟭 P.Algebra := by
  subst F
  letI : (𝟭 (Complex A)).LaxMonoidal := b.toLaxMonoidal
  have hp (X : Complex A) (n : ℕ) :
      laxPowerComparison (𝟭 (Complex A)) X n = 𝟙 (power X n) := by
    induction n with
    | zero => exact eq_of_heq hε
    | succ n ih =>
      change (X ◁ laxPowerComparison (𝟭 (Complex A)) X n) ≫
        μ (𝟭 (Complex A)) X (power X n) = 𝟙 (X ⊗ power X n)
      rw [ih, eq_of_heq (hμ X (power X n))]
      let Z := X ⊗ power X n
      exact (congrArg (fun t : Z ⟶ Z => t ≫ 𝟙 Z)
        (MonoidalCategory.whiskerLeft_id X (power X n))).trans (Category.id_comp _)
  refine NatIso.ofComponents (fun X => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (Iso.refl _) fun n => ?_) ?_
  · change (laxTensorComparison (𝟭 (Complex A)) (k.arity n)
      (laxPowerComparison (𝟭 (Complex A)) X.carrier n) ≫ X.action n) ≫ 𝟙 _ =
        (𝟙 (P.arity n) ⊗ₘ TensorPowers.map (𝟙 X.carrier) n) ≫ X.action n
    simp only [laxTensorComparison, eq_of_heq (hc n), hp, eq_of_heq (hμ _ _),
      TensorPowers.map_id]
    let Z := P.arity n ⊗ power X.carrier n
    let t : Z ⟶ Z := 𝟙 (P.arity n) ⊗ₘ 𝟙 (power X.carrier n)
    change ((t ≫ 𝟙 Z) ≫ X.action n) ≫ 𝟙 X.carrier = t ≫ X.action n
    exact (Category.comp_id _).trans
      (congrArg (fun k : Z ⟶ Z => k ≫ X.action n) (Category.comp_id t))
  · intro X Y a
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change a.hom ≫ 𝟙 _ = 𝟙 _ ≫ a.hom
    rw [Category.comp_id, Category.id_comp]

/-- 項別の係数制限の恒等比較。 -/
lemma complexCoefficientRestriction_id :
    R (RingHom.id S) = 𝟭 (Complex S) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y k
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

attribute [local instance] scalarRestrictionLaxBraided

/-- 厳密係数制限の恒等比較。 -/
def coefficientRestrictionIdIso (S : Type u) [CommRing S] :
    coefficientRestriction (RingHom.id S) ≅ 𝟭 (operad S).Algebra :=
  operadTransportIdentityIso (operad S) (R (RingHom.id S))
    (coefficientRestrictionComparison (RingHom.id S)) complexCoefficientRestriction_id
    (heq_of_eq restrictionUnit_id)
    (fun X Y => heq_of_eq (restrictionTensor_id X Y))
    (fun n => heq_of_eq (coefficientComplexMap_id n))

/-- 厳密係数制限の合成比較。 -/
def coefficientRestrictionCompIso :
    coefficientRestriction (g.comp f) ≅ coefficientRestriction g ⋙ coefficientRestriction f := by
  refine NatIso.ofComponents (fun X => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (Iso.refl _) fun n => ?_) ?_
  · simp only [Iso.refl_hom, Category.comp_id, TensorPowers.map_id, tensorHom_id,
      id_whiskerRight, Category.id_comp]
    exact coefficientRestriction_comp_action f g X n
  · intro X Y k
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    change (R (g.comp f)).map k.hom ≫ 𝟙 _ = 𝟙 _ ≫ (R (g.comp f)).map k.hom
    rw [Category.comp_id, Category.id_comp]

end SerrePositivity.EInfinity.BarrattEccles
