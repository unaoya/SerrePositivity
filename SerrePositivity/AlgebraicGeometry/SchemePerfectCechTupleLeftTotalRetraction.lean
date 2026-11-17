module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalComponents

/-!
概要：元のY側の各直和の座標を戻す、次数ごとの左逆。
方針：元のCの座標の射影と同じtotalDescを使う。
規約：余分な基底の正次数を零へ送り、鎖写像とは仮定しない。
使われ方：同じ元のkernelへのtotal比較の短完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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
/-- 同じ元の直和の各脚の座標を戻し、正の外次数の基底だけを零へ送る。 -/
def schemePerfectCechTupleLeftTotalRetractionSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).X a).X b ⟶
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble g U p hp hR) up).X n := by
  let K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up := schemePerfectCechTupleDouble g U p hp hR
  cases b with
  | zero =>
    cases a with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      exact (HomologicalComplex.singleObjXSelf up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).inv ≫
        K.ιTotal up 0 0 0 (by rfl)
    | succ a => exact 0
  | succ b =>
    exact (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCπ b ≫
      K.ιTotal up (a + 1) b n (by change a + (b + 1) = n at h; change a + 1 + b = n; omega)

/-- 同じ元のtotalDescを用いる次数ごとの射。鎖写像性は主張しない。 -/
def schemePerfectCechTupleLeftTotalRetractionComponent (n : ℕ) :
    ((schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).total up).X n ⟶
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        (schemePerfectCechTupleDouble g U p hp hR) up).X n :=
  (schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).totalDesc
    (fun a b h ↦ schemePerfectCechTupleLeftTotalRetractionSummand f g F q hq U p hp hR hS a b n h)

/-- 元の各直和入射の後では、指定した同じ座標の射影になる。 -/
theorem ι_schemePerfectCechTupleLeftTotalRetractionComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    (schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS).ιTotal up a b n h ≫
        schemePerfectCechTupleLeftTotalRetractionComponent f g F q hq U p hp hR hS n =
      schemePerfectCechTupleLeftTotalRetractionSummand f g F q hq U p hp hR hS a b n h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 元の各全次数で、同じ再索引の射の後に座標を戻すと恒等射。 -/
theorem schemePerfectCechTupleLeftTotalComponent_retraction (n : ℕ) :
    schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n ≫
        schemePerfectCechTupleLeftTotalRetractionComponent f g F q hq U p hp hR hS n = 𝟙 _ := by
  let K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up := schemePerfectCechTupleDouble g U p hp hR
  let L := schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_schemePerfectCechTupleLeftTotalComponent, Category.comp_id]
  cases a with
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      change ((HomologicalComplex.singleObjXSelf up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫ L.ιTotal up 0 0 0 _) ≫ _ = _
      have hh := ι_schemePerfectCechTupleLeftTotalRetractionComponent
        f g F q hq U p hp hR hS 0 0 0 (by rfl)
      have hc := congrArg (fun z : (L.X 0).X 0 ⟶ (K.total up).X 0 ↦
        (HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫ z) hh
      refine (Category.assoc _ _ _).trans (hc.trans ?_)
      change (HomologicalComplex.singleObjXSelf up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫
        ((HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).inv ≫ K.ιTotal up 0 0 0 _) = _
      simp only [Iso.hom_inv_id_assoc]
      rfl
    | succ b =>
      exact (HomologicalComplex.isZero_single_obj_X up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) (b + 1) (by omega)).eq_of_src _ _
  | succ a =>
    change ((schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCι b ≫
      L.ιTotal up a (b + 1) n _) ≫ _ = _
    rw [Category.assoc, ι_schemePerfectCechTupleLeftTotalRetractionComponent]
    change (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCι b ≫
      ((schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌).leftCπ b ≫
        K.ιTotal up (a + 1) b n _) = _
    rw [← Category.assoc, CechAugmentedSquare.leftCι_π, Category.id_comp]

end SerrePositivity.AlgebraicGeometry
