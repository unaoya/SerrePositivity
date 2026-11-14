module

public import SerrePositivity.BhattScholze.Prismatic.Site.FlatSiteResidue
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCechSheaf
import all SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
import SerrePositivity.CommutativeAlgebra.CompletelyFlat.FiniteIdealReduction
public import SerrePositivity.HomologicalAlgebra.Cech.InverseTower
import all SerrePositivity.HomologicalAlgebra.Cech.InverseTower
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# 完備 Čech 複体の有限剰余の逆極限

## 概要
各次数で有限剰余の逆極限として計算できる構造環の増大 Čech 複体は完全。

## 方針
通常の忠実平坦な Čech 完全性を有限段へ移し、全射的な逆塔の完全性を使う。

## 規約
BS 著者版 Corollary 3.12 (c)。増大を次数零に置く。

## 使われ方
構造前層と prism イデアルによる剰余前層の完備 Čech 降下。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.Cech

open CategoryTheory CategoryTheory.Limits DerivedCompletion

variable {S : Type v} [CommRing S]

/-- 概要：逆塔への両立する余鎖写像が各次数で逆極限を与えると、複体の同型を得る。
方針：次数ごとの極限への線形写像を取り、全ての射影で微分との可換性を確認する。
規約：自然数次数の通常の余鎖複体。
使われ方：完備 Čech 複体を有限剰余の逆極限と同定する。 -/
def degreewiseTowerIsoOfBijective
    (C : CochainComplex (ModuleCat.{u} S) ℕ)
    (K : ℕ → CochainComplex (ModuleCat.{u} S) ℕ) (t : ∀ n, K (n + 1) ⟶ K n)
    (q : ∀ n, C ⟶ K n) (hq : ∀ n, q (n + 1) ≫ t n = q n)
    (hlim : ∀ j, Function.Bijective
      (moduleTowerLimitLift S (fun n ↦ (K n).X j) (fun n ↦ ((t n).f j).hom)
        (C.X j) (fun n ↦ ((q n).f j).hom)
        (fun n ↦ congrArg (fun g : C ⟶ K n ↦ (g.f j).hom) (hq n)))) :
    C ≅ degreewiseTowerLimit K t := by
  let l (j : ℕ) := moduleTowerLimitLift S (fun n ↦ (K n).X j) (fun n ↦ ((t n).f j).hom)
    (C.X j) (fun n ↦ ((q n).f j).hom)
    (fun n ↦ congrArg (fun g : C ⟶ K n ↦ (g.f j).hom) (hq n))
  let w : C ⟶ degreewiseTowerLimit K t :=
    CochainComplex.ofHom (fun j ↦ ModuleCat.ofHom (l j)) (fun j ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext n
      have hproj := DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom ((degreewiseTowerProjection K t n).comm j (j + 1))) (l j x)
      have hn := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((q n).comm j (j + 1))) x
      exact hproj.symm.trans hn)
  letI : ∀ j : ℕ, IsIso (w.f j) := fun j ↦
    (ConcreteCategory.isIso_iff_bijective (w.f j)).mpr (hlim j)
  letI : IsIso w := HomologicalComplex.Hom.isIso_of_components w
  exact asIso w

end SerrePositivity.Cech

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}
variable {X Y : PrismOver P R κ}

/-- 基底対象の p と向きの生成元が張る完備化イデアル。 -/
abbrev flatPairIdeal (X : PrismOver P R κ) : Ideal X.B :=
  Ideal.span {(p : X.B), X.Q.generator}

private def intModules : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj G := ModuleCat.of ℤ G
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

private instance : intModules.{u}.Additive where
  map_add := rfl

private def intCech :
    CosimplicialObject.Augmented CommRingCat.{u} ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  CosimplicialObject.Augmented.whiskeringObj _ _ (Cech.ringToAb ⋙ intModules) ⋙
    Cech.augmentedCochain

private theorem intCech_acyclic_iff (S : CosimplicialObject.Augmented CommRingCat.{u}) :
    (intCech.obj S).Acyclic ↔ Cech.AugmentedRingCechExact S := by
  rw [Cech.ringCechExact_iff_acyclic]
  have hF (T : ShortComplex AddCommGrpCat.{u}) :
      (T.map intModules).Exact ↔ T.Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
      ShortComplex.ab_exact_iff_function_exact]
    rfl
  rw [← Cech.acyclic_map_iff_of_exact intModules _ hF]
  let e := Cech.mapAugmentedCochainIso intModules
    ((CosimplicialObject.Augmented.whiskeringObj _ _ Cech.ringToAb).obj S)
  exact ⟨fun h j ↦ (h j).of_iso e.symm, fun h j ↦ (h j).of_iso e⟩

private abbrev standardResidueArrow (f : X ⟶ Y) (J : Ideal X.B) :=
  Arrow.mk (@residueHom (CommRingCat.of X.B) (CommRingCat.of Y.B) J (structureRing.map f))

private def finiteResidueArrowIso (f : X ⟶ Y) (J : Ideal X.B) :
    standardResidueArrow f J ≅ flatResidueArrow f J := by
  let e := Ideal.quotientEquiv J (J.map (RingHom.id X.B)) (RingEquiv.refl X.B) rfl
  refine Arrow.isoMk e.toCommRingCatIso (Iso.refl _) ?_
  simp only [Iso.refl_hom, Category.comp_id]
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  ext x
  change Ideal.Quotient.mk _ (((Under.mkIdInitial (X := X)).to (Under.mk f)).right.toHom.toRingHom x)
    = Ideal.Quotient.mk _ (f.toHom.toRingHom x)
  rw [Under.mkIdInitial_to_right] <;> rfl

private theorem finiteResidue_exact (hκ : IsAdmissibleCutoff P R κ) (f : X ⟶ Y)
    (hf : IsFaithfullyFlat f) (J : Ideal X.B) (n : ℕ) (hJ : flatPairIdeal X ^ n ≤ J) :
    (intCech.obj (flatResidueCech hκ f hf J)).Acyclic := by
  let := f.toHom.toRingHom.toAlgebra
  let a := standardResidueArrow f J
  have hff : letI := a.hom.hom.toAlgebra; Module.FaithfullyFlat a.left a.right := by
    change @Module.FaithfullyFlat (X.B ⧸ J) (Y.B ⧸ J.map f.toHom.toRingHom) _ _
      a.hom.hom.toAlgebra.toModule
    have he : a.hom.hom.toAlgebra = adicQuotientAlgebra J Y.B := by
      apply Algebra.algebra_ext
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [he]
    exact faithfullyFlat_algebraQuotient_of_idealPower_le _ J Y.B hf n hJ
  have hcech := Cech.isCechExact_of_faithfullyFlat (Under.mk a.hom) hff
  have h₁ : (p : X.B) ^ n ∈ J :=
    hJ (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
  have h₂ : X.Q.generator ^ n ∈ J :=
    hJ (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _)
  let e := (CosimplicialObject.augmentedCechConerve.mapIso (finiteResidueArrowIso f J)) ≪≫
    (flatResidueCechIso hκ f hf J (flatResidueCoconeIsColimit hκ f hf J n n h₁ h₂)).symm
  have hx := (intCech_acyclic_iff a.augmentedCechConerve).mpr hcech
  exact fun j ↦ (hx j).of_iso (intCech.mapIso e)

private def cechMap (hκ : IsAdmissibleCutoff P R κ) (f : X ⟶ Y) (hf : IsFaithfullyFlat f)
    {F G : Under X ⥤ CommRingCat.{u}} (α : F ⟶ G) :
    (CosimplicialObject.Augmented.whiskeringObj _ _ F).obj (flatCechUnder hκ f hf) ⟶
      (CosimplicialObject.Augmented.whiskeringObj _ _ G).obj (flatCechUnder hκ f hf) :=
  ((CosimplicialObject.Augmented.whiskering _ _).map α).app (flatCechUnder hκ f hf)

/-- 概要：有限剰余の逆極限で計算される完備 Čech 複体は全次数で完全。
方針：通常の忠実平坦降下と次数ごとに全射的な逆塔を組み合わせる。
規約：基底イデアルの列は (p,d) の冪を各段で含む。比較は各項の標準剰余射。
使われ方：構造環では (p,d) の冪、d 剰余では (d,pⁿ) を使う。 -/
theorem flatRingCechExact_of_residues (hκ : IsAdmissibleCutoff P R κ) (f : X ⟶ Y)
    (hf : IsFaithfullyFlat f) (F : PrismOver P R κ ⥤ CommRingCat.{u})
    (J : ℕ → Ideal X.B) (hJ : Antitone J) (hfinite : ∀ n, ∃ m, flatPairIdeal X ^ m ≤ J n)
    (π : ∀ n, Under.forget X ⋙ F ⟶ flatResidueRing (J n))
    (hπ : ∀ n, π (n + 1) ≫ flatResidueTransition (hJ n.le_succ) = π n)
    (hlim : ∀ (Z : Under X) (a : ∀ n, (flatResidueRing (J n)).obj Z),
      (∀ n, (flatResidueTransition (hJ n.le_succ)).app Z (a (n + 1)) = a n) →
        ∃! z : F.obj Z.right, ∀ n, (π n).app Z z = a n) :
    Cech.AugmentedRingCechExact (flatRingCech hκ F f hf) := by
  let K (n : ℕ) := intCech.obj (flatResidueCech hκ f hf (J n))
  let t (n : ℕ) : K (n + 1) ⟶ K n :=
    intCech.map (flatResidueCechTransition hκ f hf (hJ n.le_succ))
  let C := intCech.obj (flatRingCech hκ F f hf)
  let q (n : ℕ) : C ⟶ K n := intCech.map (cechMap hκ f hf (π n))
  have hq (n : ℕ) : q (n + 1) ≫ t n = q n := by
    rw [← intCech.map_comp]
    apply congrArg intCech.map
    rw [← hπ n]
    apply Comma.hom_ext <;> rfl
  apply (intCech_acyclic_iff _).mp
  have hsurj : ∀ n j, Function.Surjective ((t n).f j) := by
    intro n j
    have hfactor (Z : Under X) : Function.Surjective
        ((flatResidueTransition (hJ n.le_succ)).app Z) := by
      let b := Z.hom.toHom.toRingHom
      exact Ideal.Quotient.factor_surjective
        (show (J (n + 1)).map b ≤ (J n).map b from Ideal.map_mono (hJ n.le_succ))
    cases j with
    | zero => exact hfactor (Under.mk (𝟙 X))
    | succ j => exact hfactor ((flatCechUnder hκ f hf).right.obj ⦋j⦌)
  have hstage (n : ℕ) : (K n).Acyclic := by
    obtain ⟨m, hm⟩ := hfinite n
    exact finiteResidue_exact hκ f hf (J n) m hm
  have hbij (j : ℕ) : Function.Bijective
      (DerivedCompletion.moduleTowerLimitLift ℤ (fun n ↦ (K n).X j) (fun n ↦ ((t n).f j).hom)
        (C.X j) (fun n ↦ ((q n).f j).hom)
        (fun n ↦ congrArg (fun g : C ⟶ K n ↦ (g.f j).hom) (hq n))) := by
    have hterm : ∀ a : ∀ n, (K n).X j,
        (∀ n, (t n).f j (a (n + 1)) = a n) →
          ∃! z : C.X j, ∀ n, (q n).f j z = a n := by
      cases j with
      | zero => exact hlim (Under.mk (𝟙 X))
      | succ j => exact hlim ((flatCechUnder hκ f hf).right.obj ⦋j⦌)
    constructor
    · intro x y hxy
      have h (n : ℕ) : (q n).f j x = (q n).f j y := congrArg (fun a ↦ a.val n) hxy
      obtain ⟨_, _, hu⟩ := hterm (fun n ↦ (q n).f j x) (fun n ↦ by
        exact DFunLike.congr_fun (congrArg (fun k : C ⟶ K n ↦ (k.f j).hom) (hq n)) x)
      exact (hu x (fun _ ↦ rfl)).trans (hu y (fun n ↦ (h n).symm)).symm
    · intro a
      obtain ⟨x, hx, _⟩ := hterm a.val ((DerivedCompletion.mem_moduleTowerLimit_iff ℤ _ _ _).mp a.property)
      exact ⟨x, Subtype.ext (funext hx)⟩
  let e := Cech.degreewiseTowerIsoOfBijective C K t q hq hbij
  exact fun j ↦ ((Cech.degreewiseTowerLimit_acyclic K t hsurj hstage) j).of_iso e.symm

end SerrePositivity.BhattScholze.Prismatic.PrismOver
