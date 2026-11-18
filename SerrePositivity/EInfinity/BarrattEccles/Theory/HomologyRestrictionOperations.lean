module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyRestrictionClasses
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientMonoidAction

/-!
# Barratt–Eccles の零次演算と係数制限

## 概要
Berger–Fresse §1 の積と単位の代表を、制限した係数と元の係数で比べる。

## 方針
同じ augmentation を持つ演算係数を鎖ホモトピーで比較する。

## 規約
係数の収縮は群同変であることを要求しない。比較は実際の H⁰ の類に対して行う。

## 使われ方
M13 の `pi0_restrict`。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded TensorPowers _root_.SerrePositivity.HomologyZero
open Functor.LaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

local notation "R" => ScalarExtension.restriction f
local notation "M" => ModuleCat.restrictScalars f

private def restrictionAritySectionHomotopy (n : ℕ) :
    Homotopy (aritySection S n ≫ coefficientComplexMap f n)
      (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f (aritySection T n)) := by
  let a := aritySection S n ≫ coefficientComplexMap f n
  let b := _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f (aritySection T n)
  let e := complexContraction T n
  have h₁ : a ≫ (R).map e.hom = ε R := by
    have hc := coefficientComplexMap_augmentation f n
    change (augmentation S).map.app (FiniteBijection.of n) ≫ ε R =
      coefficientComplexMap f n ≫ (R).map e.hom at hc
    simp only [a, Category.assoc]
    rw [← hc, ← Category.assoc, aritySection_augmentation, Category.id_comp]
  have h₂ : b ≫ (R).map e.hom = ε R := by
    change (ε R ≫ (R).map (aritySection T n)) ≫ (R).map e.hom = _
    rw [Category.assoc, ← (R).map_comp]
    change ε R ≫ (R).map (aritySection T n ≫
      (augmentation T).map.app (FiniteBijection.of n)) = _
    rw [aritySection_augmentation, (R).map_id, Category.comp_id]
  have h : Homotopy ((R).map (e.hom ≫ e.inv)) ((R).map (𝟙 (complex T n))) :=
    (M).mapHomotopy e.homotopyHomInvId
  rw [(R).map_comp, (R).map_id] at h
  have k : a ≫ ((R).map e.hom ≫ (R).map e.inv) = b ≫ ((R).map e.hom ≫ (R).map e.inv) := by
    rw [← Category.assoc, h₁, ← Category.assoc, h₂]
  exact (h.compLeftId a).symm.trans ((Homotopy.ofEq k).trans (h.compLeftId b))

private lemma restrictedUnitPairing {K L N : Complex T} (m : K ⊗ L ⟶ N)
    (a : 𝟙_ (Complex T) ⟶ K) (b : 𝟙_ (Complex T) ⟶ L) :
    _root_.SerrePositivity.HomologyZero.unitPairing (μ R K L ≫ (R).map m) (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f a) (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b) =
      _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f (_root_.SerrePositivity.HomologyZero.unitPairing m a b) := by
  change (λ_ (𝟙_ (Complex S))).inv ≫
      ((ε R ≫ (R).map a) ⊗ₘ (ε R ≫ (R).map b)) ≫ μ R K L ≫ (R).map m =
    ε R ≫ (R).map ((λ_ (𝟙_ (Complex T))).inv ≫ (a ⊗ₘ b) ≫ m)
  have h :
      (λ_ (𝟙_ (Complex S))).inv ≫ (ε R ⊗ₘ ε R) ≫ μ R _ _ =
        ε R ≫ (R).map (λ_ (𝟙_ (Complex T))).inv := by
    rw [tensorHom_def'_assoc, ← leftUnitor_inv_naturality_assoc, left_unitality_inv]
  rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, reassoc_of% h]
  simp only [(R).map_comp]

private lemma restrictedOperation_value (X : (operad T).Algebra) (n : ℕ)
    (a : 𝟙_ (Complex S) ⟶ power ((R).obj X.carrier) n) :
    a ≫ homologyOperation ((coefficientRestriction f).obj X) n =
      _root_.SerrePositivity.HomologyZero.unitPairing (μ R ((operad T).arity n) (power X.carrier n) ≫ (R).map (X.action n))
        (aritySection S n ≫ coefficientComplexMap f n)
        (a ≫ laxPowerComparison R X.carrier n) := by
  change a ≫ (λ_ _).inv ≫ (aritySection S n ▷ _) ≫
      (coefficientComplexMap f n ⊗ₘ laxPowerComparison R X.carrier n) ≫
        μ R _ _ ≫ (R).map (X.action n) = _
  rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rfl

private lemma restrictedOperation_class (X : (operad T).Algebra) (n : ℕ)
    (a : 𝟙_ (Complex S) ⟶ power ((R).obj X.carrier) n)
    (b : 𝟙_ (Complex T) ⟶ power X.carrier n)
    (h : a ≫ laxPowerComparison R X.carrier n = _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b) :
    ((exactCochainHomologyIso M 0).hom.app X.carrier)
      (_root_.SerrePositivity.HomologyZero.unitClass ((R).obj X.carrier) (a ≫ homologyOperation ((coefficientRestriction f).obj X) n)) =
      _root_.SerrePositivity.HomologyZero.unitClass X.carrier (b ≫ homologyOperation X n) := by
  let k := μ R ((operad T).arity n) (power X.carrier n) ≫ (R).map (X.action n)
  rw [restrictedOperation_value, h]
  have he : _root_.SerrePositivity.HomologyZero.unitClass ((R).obj X.carrier)
      (_root_.SerrePositivity.HomologyZero.unitPairing k (aritySection S n ≫ coefficientComplexMap f n) (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b)) =
        _root_.SerrePositivity.HomologyZero.unitClass ((R).obj X.carrier)
          (_root_.SerrePositivity.HomologyZero.unitPairing k (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f (aritySection T n)) (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b)) :=
    (_root_.SerrePositivity.HomologyZero.unitClass_eq_iff _ _ _).mpr
      ⟨_root_.SerrePositivity.HomologyZero.unitPairingHomotopy k (restrictionAritySectionHomotopy f n)
        (Homotopy.refl (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b))⟩
  rw [he, restrictedUnitPairing, _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap_class]
  congr 1
  simp only [_root_.SerrePositivity.HomologyZero.unitPairing, LinearMap.coe_mk, AddHom.coe_mk, homologyOperation]
  rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]

/-- The exact homology comparison sends the restricted nullary operation to the original unit. -/
lemma restrictedHomologyOne (X : (operad T).Algebra) :
    ((exactCochainHomologyIso M 0).hom.app X.carrier)
      (homologyOne ((coefficientRestriction f).obj X)) = homologyOne X := by
  change ((exactCochainHomologyIso M 0).hom.app X.carrier)
    (_root_.SerrePositivity.HomologyZero.unitClass ((R).obj X.carrier) (homologyOperation ((coefficientRestriction f).obj X) 0)) =
      _root_.SerrePositivity.HomologyZero.unitClass X.carrier (homologyOperation X 0)
  simpa only [Category.id_comp] using
    restrictedOperation_class f X 0 (𝟙 _) (𝟙 _) (by
      change 𝟙 _ ≫ ε R = ε R ≫ (R).map (𝟙 _)
      rw [Category.id_comp, (R).map_id, Category.comp_id])

private lemma restrictedPowerTwo (K : Complex T) :
    ((R).obj K ◁ (oneIso ((R).obj K)).inv) ≫ laxPowerComparison R K 2 =
      μ R K K ≫ (R).map (K ◁ (oneIso K).inv) := by
  have h : (oneIso ((R).obj K)).inv ≫ laxPowerComparison R K 1 =
      (R).map (oneIso K).inv := by
    apply (cancel_mono ((R).map (oneIso K).hom)).mp
    rw [Category.assoc, laxPowerComparison_one, Iso.inv_hom_id,
      ← (R).map_comp, Iso.inv_hom_id, (R).map_id]
  change ((R).obj K ◁ (oneIso ((R).obj K)).inv) ≫
    ((R).obj K ◁ laxPowerComparison R K 1) ≫ μ R K (power K 1) = _
  rw [← whiskerLeft_comp_assoc, h, μ_natural_right]

set_option maxHeartbeats 800000 in
-- Elaborate both tensor powers of the same complex under different scalar actions.
/-- 正確なホモロジー比較は、係数を制限した二入力の積を保つ。 -/
lemma restrictedHomologyProduct (X : (operad T).Algebra)
    (x y : ((coefficientRestriction f).obj X).carrier.homology 0) :
    let e : ((coefficientRestriction f).obj X).carrier.homology 0 ⟶
      (M).obj (X.carrier.homology 0) := (exactCochainHomologyIso M 0).hom.app X.carrier
    e (_root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary ((coefficientRestriction f).obj X)) x y) =
      _root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X) (e x) (e y) := by
  obtain ⟨a', rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective ((R).obj X.carrier) x
  obtain ⟨b', rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective ((R).obj X.carrier) y
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap_surjective f X.carrier a'
  obtain ⟨b, rfl⟩ := _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap_surjective f X.carrier b'
  let Y := (coefficientRestriction f).obj X
  let E : ((R).obj X.carrier).homology 0 ⟶ (M).obj (X.carrier.homology 0) :=
    (exactCochainHomologyIso M 0).hom.app X.carrier
  let aₛ := _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f a
  let bₛ := _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f b
  let s := _root_.SerrePositivity.HomologyZero.unitPairing ((R).obj X.carrier ◁ (oneIso ((R).obj X.carrier)).inv) aₛ bₛ
  let t := _root_.SerrePositivity.HomologyZero.unitPairing (X.carrier ◁ (oneIso X.carrier).inv) a b
  have h : s ≫ laxPowerComparison R X.carrier 2 = _root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap f t := by
    simp only [s, t, _root_.SerrePositivity.HomologyZero.unitPairing, LinearMap.coe_mk, AddHom.coe_mk, Category.assoc]
    let U := 𝟙_ (Complex S)
    let v : U ⟶ (R).obj X.carrier ⊗ (R).obj X.carrier := (λ_ U).inv ≫ (aₛ ⊗ₘ bₛ)
    have hv : (λ_ U).inv ≫ (aₛ ⊗ₘ bₛ) ≫
        ((R).obj X.carrier ◁ (oneIso ((R).obj X.carrier)).inv) ≫
          laxPowerComparison R X.carrier 2 =
      (λ_ U).inv ≫ (aₛ ⊗ₘ bₛ) ≫ μ R X.carrier X.carrier ≫
        (R).map (X.carrier ◁ (oneIso X.carrier).inv) := by
      simpa only [v, Category.assoc] using
        congrArg (fun k => v ≫ k) (restrictedPowerTwo f X.carrier)
    exact hv.trans (restrictedUnitPairing f (X.carrier ◁ (oneIso X.carrier).inv) a b)
  have hs : _root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary Y) aₛ bₛ = s ≫ homologyOperation Y 2 := by
    simp only [s, _root_.SerrePositivity.HomologyZero.unitPairing, LinearMap.coe_mk, AddHom.coe_mk, homologyBinary, Category.assoc]
    rfl
  have ht : _root_.SerrePositivity.HomologyZero.unitPairing (homologyBinary X) a b = t ≫ homologyOperation X 2 := by
    simp only [t, _root_.SerrePositivity.HomologyZero.unitPairing, LinearMap.coe_mk, AddHom.coe_mk, homologyBinary, Category.assoc]
  have hl := _root_.SerrePositivity.HomologyZero.pairingValue_class (homologyBinary Y) aₛ bₛ
  have hr := _root_.SerrePositivity.HomologyZero.pairingValue_class (homologyBinary X) a b
  rw [hs] at hl
  rw [ht] at hr
  calc
    _ = E (_root_.SerrePositivity.HomologyZero.unitClass ((R).obj X.carrier) (s ≫ homologyOperation Y 2)) := congrArg E hl
    _ = _root_.SerrePositivity.HomologyZero.unitClass X.carrier (t ≫ homologyOperation X 2) :=
      restrictedOperation_class f X 2 s t h
    _ = _root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X) (_root_.SerrePositivity.HomologyZero.unitClass X.carrier a) (_root_.SerrePositivity.HomologyZero.unitClass X.carrier b) := hr.symm
    _ = _ := congrArg₂ (_root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary X))
      (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap_class f a).symm (_root_.SerrePositivity.EInfinity.HomologyZero.restrictionUnitMap_class f b).symm

end SerrePositivity.EInfinity.BarrattEccles
