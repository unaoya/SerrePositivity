module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalRetraction
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：元の直和入射で作った同じF8のY側の比較射の微分との可換性。
方針：元の各直和入射で二方向の微分と根の増大を照合する。
規約：元の微分の可換性を仮定として追加しない。
使われ方：元の同じkernelへの全複体の標準比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Preadditive
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ再索引の各成分は、元の全複体の微分と可換。 -/
theorem schemePerfectCechTupleLeftTotalComponent_d (n : ℕ) :
    schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n ≫
        ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).total up).d
          n (n + 1) =
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble g U p hp hR) up).d n (n + 1) ≫
          schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS (n + 1) := by
  let K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up := schemePerfectCechTupleDouble g U p hp hR
  let L := schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_schemePerfectCechTupleLeftTotalComponent]
  rw [← Category.assoc (K.ιTotal up a b n h),
    SerrePositivity.HomologicalAlgebra.total_d_summand K a b n h,
    add_comp, zsmul_comp, Category.assoc, ι_schemePerfectCechTupleLeftTotalComponent,
    Category.assoc, ι_schemePerfectCechTupleLeftTotalComponent]
  cases a with
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      let s₀ := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋0⦌
      let e : (K.X 0).X 0 ⟶ (L.X 0).X 0 :=
        (HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom
      let i₀ := L.ιTotal up 0 0 0 (by rfl)
      let i₁ := L.ιTotal up 0 1 1 (by rfl)
      change (e ≫ i₀) ≫ (L.total up).d 0 1 =
        (K.d 0 1).f 0 ≫ (s₀.leftCι 0 ≫ i₁) +
          (-1 : ℤ) ^ 0 • ((K.X 0).d 0 1 ≫ (0 : (K.X 0).X 1 ⟶ (L.total up).X 1))
      simp only [comp_zero, pow_zero, one_zsmul, add_zero]
      have hh : (L.d 0 1).f 0 = 0 :=
        schemePerfectCechTupleLeftBase_horizontal_zero f g F q hq U p hp hR hS
      have hd : i₀ ≫ (L.total up).d 0 1 = (L.X 0).d 0 1 ≫ i₁ := by
        simpa only [hh, zero_comp, zero_add, pow_zero, one_zsmul] using
          SerrePositivity.HomologicalAlgebra.total_d_summand L 0 0 0 (by rfl)
      have hv : (L.X 0).d 0 1 = ModuleCat.ofHom s₀.scalar ≫ s₀.leftCι 0 :=
        (CechAugmentedSquare.scalar_leftCι s₀).symm
      have hε : (K.d 0 1).f 0 = e ≫ ModuleCat.ofHom s₀.scalar :=
        schemePerfectCechTupleAugmentationHom_f_zero g U p hp hR ⦋0⦌
      calc
        (e ≫ i₀) ≫ (L.total up).d 0 1 = e ≫ (i₀ ≫ (L.total up).d 0 1) := Category.assoc _ _ _
        _ = e ≫ ((L.X 0).d 0 1 ≫ i₁) :=
          congrArg (fun z : (L.X 0).X 0 ⟶ (L.total up).X 1 ↦ e ≫ z) hd
        _ = e ≫ ((ModuleCat.ofHom s₀.scalar ≫ s₀.leftCι 0) ≫ i₁) :=
          congrArg (fun z : (L.X 0).X 0 ⟶ (L.X 0).X 1 ↦ e ≫ (z ≫ i₁)) hv
        _ = (K.d 0 1).f 0 ≫ (s₀.leftCι 0 ≫ i₁) := by
          simpa only [Category.assoc] using
            congrArg (fun z : (K.X 0).X 0 ⟶ s₀.C.X 0 ↦ z ≫ (s₀.leftCι 0 ≫ i₁)) hε.symm
    | succ b =>
      exact (HomologicalComplex.isZero_single_obj_X up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) (b + 1) (by omega)).eq_of_src _ _
  | succ a =>
    let sA := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
    let sB := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a + 1⦌
    let iH := L.ιTotal up (a + 1) (b + 1) (n + 1)
      (by change a + 1 + b = n at h; change a + 1 + (b + 1) = n + 1; omega)
    let iV := L.ιTotal up a (b + 2) (n + 1)
      (by change a + 1 + b = n at h; change a + (b + 2) = n + 1; omega)
    let dH : sA.C.X b ⟶ sB.C.X b := (K.d (a + 1) (a + 2)).f b
    let dV := sA.C.d b (b + 1)
    let i := L.ιTotal up a (b + 1) n
      (by change a + 1 + b = n at h; change a + (b + 1) = n; omega)
    change (sA.leftCι b ≫ i) ≫ (L.total up).d n (n + 1) =
      dH ≫ (sB.leftCι b ≫ iH) + (-1 : ℤ) ^ (a + 1) • (dV ≫ sA.leftCι (b + 1) ≫ iV)
    have hd : i ≫ (L.total up).d n (n + 1) =
        (L.d a (a + 1)).f (b + 1) ≫ iH +
          (-1 : ℤ) ^ a • ((L.X a).d (b + 1) (b + 2) ≫ iV) :=
      SerrePositivity.HomologicalAlgebra.total_d_summand L a (b + 1) n _
    have hh : sA.leftCι b ≫ (L.d a (a + 1)).f (b + 1) = dH ≫ sB.leftCι b :=
      schemePerfectCechTupleLeftCι_horizontal f g F q hq U p hp hR hS a b
    let dN : sA.C.X b ⟶ (L.X a).X (b + 2) := (-dV) ≫ sA.leftCι (b + 1)
    have hv : sA.leftCι b ≫ (L.X a).d (b + 1) (b + 2) = dN := by
      exact (CechAugmentedSquare.leftCι_d sA b).trans
        (Preadditive.neg_comp dV (sA.leftCι (b + 1))).symm
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun z : (L.X a).X (b + 1) ⟶ (L.total up).X (n + 1) ↦
      sA.leftCι b ≫ z) hd).trans ?_
    calc
      _ = (sA.leftCι b ≫ (L.d a (a + 1)).f (b + 1)) ≫ iH +
          (-1 : ℤ) ^ a • ((sA.leftCι b ≫ (L.X a).d (b + 1) (b + 2)) ≫ iV) := by
        simp only [comp_add, comp_zsmul, Category.assoc]
      _ = (dH ≫ sB.leftCι b) ≫ iH +
          (-1 : ℤ) ^ a • (dN ≫ iV) :=
        congrArg₂ (fun x y : sA.C.X b ⟶ (L.total up).X (n + 1) ↦ x + y)
          (congrArg (fun z : sA.C.X b ⟶ (L.X (a + 1)).X (b + 1) ↦ z ≫ iH) hh)
          (congrArg (fun z : sA.C.X b ⟶ (L.X a).X (b + 2) ↦ (-1 : ℤ) ^ a • (z ≫ iV)) hv)
      _ = dH ≫ (sB.leftCι b ≫ iH) +
          (-1 : ℤ) ^ (a + 1) • (dV ≫ sA.leftCι (b + 1) ≫ iV) := by
        simp only [dN, neg_comp, Category.assoc, smul_neg, pow_succ, mul_neg, mul_one, neg_smul]

/-- 同じ元の成分と検証した微分の式を持つ、F8のY側への全複体の射。 -/
def schemePerfectCechTupleLeftTotalMap :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble g U p hp hR) up ⟶
      (schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).total up where
  f := schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS
  comm' n m hnm := by
    have hm : n + 1 = m := hnm
    subst m
    exact schemePerfectCechTupleLeftTotalComponent_d f g F q hq U p hp hR hS n

end SerrePositivity.AlgebraicGeometry
