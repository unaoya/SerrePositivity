module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.AlgebraCoefficientRestriction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoefficientExtensionOperad

/-!
# Barratt–Eccles 代数の厳密な底変更随伴

## 概要
HA §3.2.2 の底変更を、Berger–Fresse §1.1 の厳密なオペラッド代数で構成する。

## 方針
arity ごとの比較同型で代数作用を移し、モノイダル随伴の下で射の作用保存を照合する。

## 規約
環準同型に平坦性を仮定しない。

## 使われ方
M13 の導来係数拡大と導来随伴。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory DifferentialGraded TensorPowers
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

attribute [local instance] scalarExtensionLaxBraided scalarRestrictionLaxBraided

/-- arity ごとの係数拡大の逆同型が、移送する作用を指定する。 -/
def coefficientExtensionComparison :
    Operad.LaxComparison (ScalarExtension.extension f) (operad T) (operad S) where
  arity n := (coefficientExtensionArityIso f n).inv
  permutation := coefficientExtension_permutation f
  unit := coefficientExtension_unit f
  comp := coefficientExtension_partialComposition f

/-- 厳密な係数拡大は複体の項別係数拡大を底に持つ。 -/
def coefficientExtension : (operad S).Algebra ⥤ (operad T).Algebra :=
  Operad.transport (coefficientExtensionComparison f)

/-- 作用を保つ条件は底のモノイダル随伴の下で同値。 -/
lemma coefficientAlgebraHom_mate (X : (operad S).Algebra) (Y : (operad T).Algebra)
    (g : (ScalarExtension.extension f).obj X.carrier ⟶ Y.carrier) (n : ℕ) :
    let g' := ((ScalarExtension.adjunction f).homEquiv X.carrier Y.carrier) g
    (((coefficientExtension f).obj X).action n ≫ g =
      (𝟙 ((operad T).arity n) ⊗ₘ TensorPowers.map g n) ≫ Y.action n) ↔
    (X.action n ≫ g' =
      (𝟙 ((operad S).arity n) ⊗ₘ TensorPowers.map g' n) ≫
        ((coefficientRestriction f).obj Y).action n) := by
  let L := ScalarExtension.extension f
  let R := ScalarExtension.restriction f
  let A := ScalarExtension.adjunction f
  let K := X.carrier
  let U := Y.carrier
  let P := (operad S).arity n
  let Q := (operad T).arity n
  let e : L.obj P ≅ Q := coefficientExtensionIso f n
  let c : P ⟶ R.obj Q := coefficientComplexMap f n
  let p := laxPowerComparison L K n
  let q := laxPowerComparison R U n
  let g' : K ⟶ R.obj U := (A.homEquiv K U) g
  let a := laxTensorComparison L e.inv p
  have hpIso : IsIso p := laxPowerComparison_isIso L K n
  have haIso : IsIso a := by
    let e' := (e.symm ⊗ᵢ asIso p) ≪≫ Functor.Monoidal.μIso L P (power K n)
    exact e'.isIso_hom
  have hm : (A.homEquiv P Q).symm c = e.hom := rfl
  let m := (A.homEquiv (power K n) (power U n)).symm (TensorPowers.map g' n ≫ q)
  have hp : p ≫ m = TensorPowers.map g n := laxPowerComparison_mate A g n
  change (a ≫ L.map (X.action n)) ≫ g =
      (𝟙 Q ⊗ₘ TensorPowers.map g n) ≫ Y.action n ↔
    X.action n ≫ g' = (𝟙 P ⊗ₘ TensorPowers.map g' n) ≫
      laxTensorComparison R c q ≫ R.map (Y.action n)
  have hright :
      (𝟙 P ⊗ₘ TensorPowers.map g' n) ≫ laxTensorComparison R c q =
        laxTensorComparison R c (TensorPowers.map g' n ≫ q) := by
    simp only [laxTensorComparison, tensorHom_comp_tensorHom_assoc, Category.id_comp]
  rw [reassoc_of% hright, ← (A.homEquiv (P ⊗ power K n) U).symm.injective.eq_iff,
    A.homEquiv_naturality_left_symm, A.homEquiv_naturality_right_symm,
    laxTensorComparison_mate A, Equiv.symm_apply_apply, hm, ← cancel_epi a]
  change (a ≫ L.map (X.action n)) ≫ g = (𝟙 Q ⊗ₘ TensorPowers.map g n) ≫ Y.action n ↔
    a ≫ L.map (X.action n) ≫ g = a ≫ δ L P (power K n) ≫ (e.hom ⊗ₘ m) ≫ Y.action n
  simp only [a, laxTensorComparison, Category.assoc]
  have hμ := Functor.Monoidal.μ_δ_assoc L P (power K n) ((e.hom ⊗ₘ m) ≫ Y.action n)
  rw [hμ, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, hp]

/-- 底の随伴の Hom 同値は、代数作用を保存する射に制限される。 -/
def coefficientAlgebraHomEquiv (X : (operad S).Algebra) (Y : (operad T).Algebra) :
    ((coefficientExtension f).obj X ⟶ Y) ≃ (X ⟶ (coefficientRestriction f).obj Y) where
  toFun g :=
    ⟨((ScalarExtension.adjunction f).homEquiv X.carrier Y.carrier) g.hom,
      fun n => (coefficientAlgebraHom_mate f X Y g.hom n).mp (g.comm n)⟩
  invFun h :=
    ⟨((ScalarExtension.adjunction f).homEquiv X.carrier Y.carrier).symm h.hom,
      fun n => (coefficientAlgebraHom_mate f X Y _ n).mpr (by
        simpa only [Equiv.apply_symm_apply] using h.comm n)⟩
  left_inv g := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (Equiv.symm_apply_apply _ _)
  right_inv h := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (Equiv.apply_symm_apply _ _)

/-- HA §3.2.2 の底変更随伴の厳密な模型。 -/
def coefficientAlgebraAdjunction : coefficientExtension f ⊣ coefficientRestriction f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := coefficientAlgebraHomEquiv f
    homEquiv_naturality_left_symm := by
      intro X' X Y k h
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
      exact (ScalarExtension.adjunction f).homEquiv_naturality_left_symm k.hom h.hom
    homEquiv_naturality_right := by
      intro X Y Y' g k
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
      exact (ScalarExtension.adjunction f).homEquiv_naturality_right g.hom k.hom }

end SerrePositivity.EInfinity.BarrattEccles
