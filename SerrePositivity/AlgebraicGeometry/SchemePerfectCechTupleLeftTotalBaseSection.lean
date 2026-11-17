module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftBaseComponents
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalRetraction

/-!
概要：元の正次数の基底列から同じY側への、次数ごとの右逆。
方針：元のRの座標を同じ直和入射へ戻し、零の項は零へ送る。
規約：元の射影のまま計算し、右逆を鎖写像とは主張しない。
使われ方：同じ元のkernelへの比較の短完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Preadditive
open scoped ZeroObject Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
local notation "KK" => (schemePerfectCechTupleDouble g U p hp hR :
  HomologicalComplex₂ (ModuleCat ℤ) up up)
local notation "LL" => schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS
local notation "BB" => schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS
local notation "QQ" => (cechConstantPositiveDouble BB : HomologicalComplex₂ (ModuleCat ℤ) up up)
local notation "PP" => schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS

set_option backward.isDefEq.respectTransparency false in
private theorem cechLeftBasePositive_isZero (b : ℕ) : IsZero ((BB).X (b + 1)) := by
  let s := (schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋0⦌).baseSquare
  have hC : IsZero (s.C.X b) := by
    change IsZero ((0 : CochainComplex (ModuleCat.{u} ℤ) ℕ).X b)
    exact (HomologicalComplex.eval (ModuleCat.{u} ℤ) up b).map_isZero (isZero_zero _)
  exact IsZero.of_iso hC (s.leftCIso b).symm

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底の正の外次数のRだけを同じY側の直和へ入れる各脚。 -/
def schemePerfectCechTupleLeftTotalBaseSectionSummand (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    ((QQ).X a).X b ⟶ (HomologicalComplex₂.total LL up).X n := by
  cases a with
  | zero => exact 0
  | succ a =>
    cases b with
    | zero => exact HomologicalComplex₂.ιTotal LL up (a + 1) 0 n h
    | succ b => exact 0

/-- 元の同じtotalDescで作る次数ごとの右逆。鎖写像とは主張しない。 -/
def schemePerfectCechTupleLeftTotalBaseSectionComponent (n : ℕ) :
    (HomologicalComplex₂.total QQ up).X n ⟶ (HomologicalComplex₂.total LL up).X n :=
  HomologicalComplex₂.totalDesc QQ (fun a b h ↦
    schemePerfectCechTupleLeftTotalBaseSectionSummand f g F q hq U p hp hR hS a b n h)

/-- 元の各直和入射では指定した同じ基底の脚になる。 -/
theorem ι_schemePerfectCechTupleLeftTotalBaseSectionComponent (a b n : ℕ)
    (h : ComplexShape.π up up up (a, b) = n) :
    HomologicalComplex₂.ιTotal QQ up a b n h ≫ schemePerfectCechTupleLeftTotalBaseSectionComponent f g F q hq U p hp hR hS n =
      schemePerfectCechTupleLeftTotalBaseSectionSummand f g F q hq U p hp hR hS a b n h :=
  HomologicalComplex₂.ι_totalDesc _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 同じ各全次数で、基底の右逆の後に元の射影を取ると恒等射。 -/
theorem schemePerfectCechTupleLeftTotalBaseSection_projection (n : ℕ) :
    schemePerfectCechTupleLeftTotalBaseSectionComponent f g F q hq U p hp hR hS n ≫
      (HomologicalComplex₂.total.map PP up).f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, ι_schemePerfectCechTupleLeftTotalBaseSectionComponent, Category.comp_id]
  cases a with
  | zero =>
    have hz : IsZero (((QQ).X 0).X b) := by
      change IsZero (0 : ModuleCat.{u} ℤ)
      exact isZero_zero _
    exact hz.eq_of_src _ _
  | succ a =>
    cases b with
    | zero =>
      change HomologicalComplex₂.ιTotal LL up (a + 1) 0 n h ≫ (HomologicalComplex₂.total.map PP up).f n =
        HomologicalComplex₂.ιTotal QQ up (a + 1) 0 n h
      rw [HomologicalComplex₂.ιTotal_map,
        schemePerfectCechTupleLeftBaseProjection_succ_zero f g F q hq U p hp hR hS a]
      let j : ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR) ⟶
          (HomologicalComplex₂.total QQ up).X n :=
        HomologicalComplex₂.ιTotal QQ up (a + 1) 0 n h
      change (𝟙 (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))) ≫ j = j
      exact Category.id_comp j
    | succ b =>
      exact (cechLeftBasePositive_isZero f g F q hq U p hp hR hS b).eq_of_src _ _


set_option backward.isDefEq.respectTransparency false in
/-- 同じ各全次数で、Cの座標を戻す部分と基底の部分の和は恒等射。 -/
theorem schemePerfectCechTupleLeftTotal_split (n : ℕ) :
    schemePerfectCechTupleLeftTotalRetractionComponent f g F q hq U p hp hR hS n ≫
        schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n +
      (HomologicalComplex₂.total.map PP up).f n ≫
        schemePerfectCechTupleLeftTotalBaseSectionComponent f g F q hq U p hp hR hS n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [comp_add, ← Category.assoc, ι_schemePerfectCechTupleLeftTotalRetractionComponent]
  rw [← Category.assoc (HomologicalComplex₂.ιTotal LL up a b n h), HomologicalComplex₂.ιTotal_map,
    Category.assoc, ι_schemePerfectCechTupleLeftTotalBaseSectionComponent, Category.comp_id]
  cases b with
  | zero =>
    cases a with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      rw [schemePerfectCechTupleLeftBaseProjection_zero f g F q hq U p hp hR hS 0,
        zero_comp, add_zero]
      let ei : ((LL).X 0).X 0 ⟶ ((KK).X 0).X 0 :=
        (HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).inv
      change (ei ≫ HomologicalComplex₂.ιTotal KK up 0 0 0 _) ≫
        schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS 0 = HomologicalComplex₂.ιTotal LL up 0 0 0 _
      have hh := ι_schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS 0 0 0 (by rfl)
      have hc := congrArg (fun z : ((KK).X 0).X 0 ⟶ (HomologicalComplex₂.total LL up).X 0 ↦ ei ≫ z) hh
      refine (Category.assoc _ _ _).trans (hc.trans ?_)
      change (HomologicalComplex.singleObjXSelf up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).inv ≫
        ((HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom ≫ HomologicalComplex₂.ιTotal LL up 0 0 0 _) = _
      simp only [Iso.inv_hom_id_assoc]
    | succ a =>
      rw [schemePerfectCechTupleLeftBaseProjection_succ_zero f g F q hq U p hp hR hS a]
      change (0 : ((LL).X (a + 1)).X 0 ⟶ (HomologicalComplex₂.total KK up).X n) ≫
          schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n +
        𝟙 _ ≫ HomologicalComplex₂.ιTotal LL up (a + 1) 0 n h = HomologicalComplex₂.ιTotal LL up (a + 1) 0 n h
      simp only [zero_comp, Category.id_comp, zero_add]
  | succ b =>
    have hp₀ : ((PP).f a).f (b + 1) = 0 := by
      cases a with
      | zero => exact schemePerfectCechTupleLeftBaseProjection_zero f g F q hq U p hp hR hS (b + 1)
      | succ a => exact schemePerfectCechTupleLeftBaseProjection_succ_succ f g F q hq U p hp hR hS a b
    rw [hp₀, zero_comp, add_zero]
    let sA := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
    let pc : ((LL).X a).X (b + 1) ⟶ ((KK).X (a + 1)).X b := sA.leftCπ b
    let hi : ComplexShape.π up up up (a + 1, b) = n := by
      change a + (b + 1) = n at h
      change a + 1 + b = n
      omega
    change (pc ≫ HomologicalComplex₂.ιTotal KK up (a + 1) b n hi) ≫
      schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n = HomologicalComplex₂.ιTotal LL up a (b + 1) n h
    have hh := ι_schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS (a + 1) b n hi
    have hc := congrArg (fun z : ((KK).X (a + 1)).X b ⟶ (HomologicalComplex₂.total LL up).X n ↦ pc ≫ z) hh
    refine (Category.assoc _ _ _).trans (hc.trans ?_)
    change sA.leftCπ b ≫ (sA.leftCι b ≫ HomologicalComplex₂.ιTotal LL up a (b + 1) n h) = _
    rw [← Category.assoc, CechAugmentedSquare.leftCπ_ι, Category.id_comp]

end SerrePositivity.AlgebraicGeometry
