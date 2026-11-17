module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalDifferential
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleLeftTotalBaseSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareKernelSequence

/-!
概要：元の再索引の射と元の基底射影の合成零。
方針：元の各直和入射で同じ射影の成分の式を使う。
規約：元のkernelに用いた射影と全複体を保持する。
使われ方：同じ核の標準比較に渡す短完全性。
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

local notation "KK" => (schemePerfectCechTupleDouble g U p hp hR :
  HomologicalComplex₂ (ModuleCat ℤ) up up)
local notation "LL" => schemePerfectCechTupleSquareLeftPositiveDouble f g F q hq U p hp hR hS
local notation "QQ" => (cechConstantPositiveDouble
  (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS) :
  HomologicalComplex₂ (ModuleCat ℤ) up up)
local notation "PP" => schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS

set_option backward.isDefEq.respectTransparency false in
/-- 元のY側の基底射影は正の縦次数で零。 -/
private theorem cechLeftBaseProjection_positive (a b : ℕ) : (((PP).f a).f (b + 1)) = 0 := by
  cases a with
  | zero => exact schemePerfectCechTupleLeftBaseProjection_zero f g F q hq U p hp hR hS (b + 1)
  | succ a => exact schemePerfectCechTupleLeftBaseProjection_succ_succ f g F q hq U p hp hR hS a b

set_option backward.isDefEq.respectTransparency false in
/-- 元の同じ比較射の後に、元の基底射影のtotalを取ると零。 -/
theorem schemePerfectCechTupleLeftTotalMap_baseProjection :
    schemePerfectCechTupleLeftTotalMap f g F q hq U p hp hR hS ≫
      HomologicalComplex₂.total.map PP up = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change HomologicalComplex₂.ιTotal KK up a b n h ≫
    (schemePerfectCechTupleLeftTotalComponent f g F q hq U p hp hR hS n ≫
      (HomologicalComplex₂.total.map PP up).f n) = HomologicalComplex₂.ιTotal KK up a b n h ≫ 0
  rw [← Category.assoc, ι_schemePerfectCechTupleLeftTotalComponent, comp_zero]
  cases a with
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := by change 0 + 0 = n at h; omega
      subst n
      let e : ((KK).X 0).X 0 ⟶ ((LL).X 0).X 0 :=
        (HomologicalComplex.singleObjXSelf up 0
          (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR))).hom
      change (e ≫ HomologicalComplex₂.ιTotal LL up 0 0 0 _) ≫ (HomologicalComplex₂.total.map PP up).f 0 = 0
      have hh : HomologicalComplex₂.ιTotal LL up 0 0 0 (by rfl) ≫ (HomologicalComplex₂.total.map PP up).f 0 = 0 := by
        rw [HomologicalComplex₂.ιTotal_map,
          schemePerfectCechTupleLeftBaseProjection_zero f g F q hq U p hp hR hS 0, zero_comp]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z : ((LL).X 0).X 0 ⟶ (HomologicalComplex₂.total QQ up).X 0 ↦ e ≫ z) hh).trans (comp_zero))
    | succ b =>
      exact (HomologicalComplex.isZero_single_obj_X up 0
        (ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)) (b + 1) (by omega)).eq_of_src _ _
  | succ a =>
    let sA := schemePerfectCechTupleSquare f g F q hq U p hp hR hS ⦋a⦌
    change (sA.leftCι b ≫ HomologicalComplex₂.ιTotal LL up a (b + 1) n _) ≫
      (HomologicalComplex₂.total.map PP up).f n = 0
    have hh : HomologicalComplex₂.ιTotal LL up a (b + 1) n
        (by change a + 1 + b = n at h; change a + (b + 1) = n; omega) ≫
        (HomologicalComplex₂.total.map PP up).f n = 0 := by
      rw [HomologicalComplex₂.ιTotal_map,
        cechLeftBaseProjection_positive f g F q hq U p hp hR hS a b, zero_comp]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z : ((LL).X a).X (b + 1) ⟶ (HomologicalComplex₂.total QQ up).X n ↦ sA.leftCι b ≫ z) hh).trans
        (comp_zero))

/-- 同じ元の比較射と同じ基底射影から作る短複体。短完全性は別に示す。 -/
def schemePerfectCechTupleLeftTotalShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (schemePerfectCechTupleLeftTotalMap f g F q hq U p hp hR hS)
    (HomologicalComplex₂.total.map PP up)
    (schemePerfectCechTupleLeftTotalMap_baseProjection f g F q hq U p hp hR hS)


set_option backward.isDefEq.respectTransparency false in
/-- 同じ元の三つの分裂の式を、各全次数の既存のSplittingへ代入する。 -/
def schemePerfectCechTupleLeftTotalDegreeSplitting (n : ℕ) :
    ((schemePerfectCechTupleLeftTotalShortComplex f g F q hq U p hp hR hS).map
      (HomologicalComplex.eval (ModuleCat.{u} ℤ) up n)).Splitting where
  r := schemePerfectCechTupleLeftTotalRetractionComponent f g F q hq U p hp hR hS n
  s := schemePerfectCechTupleLeftTotalBaseSectionComponent f g F q hq U p hp hR hS n
  f_r := schemePerfectCechTupleLeftTotalComponent_retraction f g F q hq U p hp hR hS n
  s_g := schemePerfectCechTupleLeftTotalBaseSection_projection f g F q hq U p hp hR hS n
  id := schemePerfectCechTupleLeftTotal_split f g F q hq U p hp hR hS n

/-- 元の同じ比較射と元の同じ基底射影の短複体は短完全。 -/
theorem schemePerfectCechTupleLeftTotal_shortExact :
    (schemePerfectCechTupleLeftTotalShortComplex f g F q hq U p hp hR hS).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (schemePerfectCechTupleLeftTotalDegreeSplitting f g F q hq U p hp hR hS n).shortExact


/-- 元のY側のtotalの完全性と、元の増大二重Čechのtotalの完全性の一致。 -/
theorem schemePerfectCechTupleLeftWholeTotal_acyclic_iff :
    (HomologicalComplex₂.total LL up).Acyclic ↔ (HomologicalComplex₂.total KK up).Acyclic := by
  have hs := schemePerfectCechTupleLeftTotal_shortExact f g F q hq U p hp hR hS
  have hq₀ := cechConstantPositiveDouble_total_acyclic
    (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS)
  constructor
  · intro hL
    apply hs.acyclic_X₁
    constructor
    intro n
    exact (_root_.quasiIsoAt_iff_exactAt _ n (hL n)).mpr (hq₀ n)
  · intro hK
    exact hs.acyclic_X₂ hK hq₀

set_option backward.isDefEq.respectTransparency false in
private theorem cechLeftOriginalKernel_shortExact :
    (ShortComplex.kernelSequence PP).ShortExact := by
  letI : Abelian (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
    inferInstanceAs (Abelian (CochainComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ) ℕ))
  letI : Epi PP := HomologicalComplex.epi_of_epi_f PP (fun a ↦
    HomologicalComplex.epi_of_epi_f _ (fun b ↦ (ModuleCat.epi_iff_surjective _).mpr
      (schemePerfectCechTupleSquarePositiveBaseLeftProjection_surjective f g F q hq U p hp hR hS a b)))
  exact { exact := ShortComplex.kernelSequence_exact PP
          mono_f := inferInstanceAs (Mono (kernel.ι PP))
          epi_g := inferInstanceAs (Epi PP) }

/-- 元の同じLeftKernelのtotalと、元の増大二重Čechのtotalの完全性の一致。 -/
theorem schemePerfectCechTupleLeftKernelTotal_acyclic_iff :
    ((schemePerfectCechTupleSquareLeftKernel f g F q hq U p hp hR hS).total up).Acyclic ↔
      (HomologicalComplex₂.total KK up).Acyclic := by
  have hs := cechIntegerLiftTotal_shortExact (ShortComplex.kernelSequence PP)
    (cechLeftOriginalKernel_shortExact f g F q hq U p hp hR hS)
  have hq₀ := cechConstantPositiveDouble_total_acyclic
    (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS)
  have he : ((schemePerfectCechTupleSquareLeftKernel f g F q hq U p hp hR hS).total up).Acyclic ↔
      (HomologicalComplex₂.total LL up).Acyclic := by
    constructor
    · intro hk
      exact hs.acyclic_X₂ hk hq₀
    · intro hL
      apply hs.acyclic_X₁
      constructor
      intro n
      exact (_root_.quasiIsoAt_iff_exactAt _ n (hL n)).mpr (hq₀ n)
  exact he.trans (schemePerfectCechTupleLeftWholeTotal_acyclic_iff f g F q hq U p hp hR hS)

end SerrePositivity.AlgebraicGeometry
