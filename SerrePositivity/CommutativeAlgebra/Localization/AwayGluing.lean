module

public import Mathlib.RingTheory.Localization.Away.Basic
import all Mathlib.RingTheory.Localization.Away.Basic

/-!
# 任意の主開局所化模型における環の貼り合わせ

## 概要
単位イデアルを生成する元の局所化上の切断を、共通主開上の両立性から貼り合わせる。

## 方針
各元の標準局所化に移し、環の既存の主開貼り合わせ定理を使う。

## 規約
局所化の模型は任意。両立性は標準主開へのすべての局所化写像について述べる。

## 使われ方
Stacks 01HR、07JJ。結晶サイトの構造環の層条件。
-/

public noncomputable section
universe u
namespace SerrePositivity.CommutativeAlgebra.Localization
variable {B : Type u} [CommRing B]
variable {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
variable [Algebra B A] [Algebra B T] [Algebra B U]

/-- 局所化の延長と、基底環上の射の合成は、直接の延長に一致する。 -/
theorem awayLift_comp (b : B) [IsLocalization.Away b A]
    (h : T →+* U) (hh : h.comp (algebraMap B T) = algebraMap B U)
    (ht : IsUnit (algebraMap B T b)) (hu : IsUnit (algebraMap B U b)) :
    h.comp (IsLocalization.Away.lift b ht : A →+* T) =
      IsLocalization.Away.lift b hu := by
  apply IsLocalization.ringHom_ext (Submonoid.powers b)
  ext r
  change h (IsLocalization.Away.lift b ht (algebraMap B A r)) =
    IsLocalization.Away.lift b hu (algebraMap B A r)
  rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
  exact DFunLike.congr_fun hh r

/-- 同じ元の二つの主開局所化を比較する延長は単射。 -/
theorem awayLift_injective (b : B) [IsLocalization.Away b A] [IsLocalization.Away b T] :
    Function.Injective (IsLocalization.Away.lift b
      (IsLocalization.Away.algebraMap_isUnit b) : A →+* T) := by
  let f : A →+* T := IsLocalization.Away.lift b (IsLocalization.Away.algebraMap_isUnit b)
  let g : T →+* A := IsLocalization.Away.lift b (IsLocalization.Away.algebraMap_isUnit b)
  have h : g.comp f = RingHom.id A := by
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    ext r
    simp only [RingHom.comp_apply, RingHom.id_apply, f, g,
      IsLocalization.Away.lift_eq]
  have hi : Function.LeftInverse g f := fun a => DFunLike.congr_fun h a
  exact hi.injective

variable {ι : Type u} (b : ι → B) (A : ι → Type u)
variable [∀ i, CommRing (A i)] [∀ i, Algebra B (A i)]
variable [∀ i, IsLocalization.Away (b i) (A i)]

/-- 主開局所化上の両立する切断は、基底環のただ一つの元から来る。 -/
theorem existsUnique_glue_away (hb : Ideal.span (Set.range b) = ⊤)
    (x : ∀ i, A i)
    (hx : ∀ (d : B) (i j : ι)
      (hi : IsUnit (algebraMap B (Localization.Away d) (b i)))
      (hj : IsUnit (algebraMap B (Localization.Away d) (b j))),
      (IsLocalization.Away.lift (b i) hi : A i →+* Localization.Away d) (x i) =
        (IsLocalization.Away.lift (b j) hj : A j →+* Localization.Away d) (x j)) :
    ∃! r : B, ∀ i, algebraMap B (A i) r = x i := by
  classical
  let s := Set.range b
  choose σ hσ using fun a : s => a.property
  have hu (a : s) : IsUnit (algebraMap B (Localization.Away a.val) (b (σ a))) := by
    rw [hσ a]
    exact IsLocalization.Away.algebraMap_isUnit a.val
  let f (a : s) : Localization.Away a.val :=
    (IsLocalization.Away.lift (b (σ a)) (hu a) : A (σ a) →+* _) (x (σ a))
  have hf (a c : s) :
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.val * c.val))
        a.val c.val (f a) =
      IsLocalization.Away.awayToAwayLeft c.val a.val (f c) := by
    have ha : IsUnit (algebraMap B (Localization.Away (a.val * c.val)) (b (σ a))) := by
      rw [hσ a]
      exact IsLocalization.Away.isUnit_of_dvd (a.val * c.val) (dvd_mul_right _ _)
    have hc : IsUnit (algebraMap B (Localization.Away (a.val * c.val)) (b (σ c))) := by
      rw [hσ c]
      exact IsLocalization.Away.isUnit_of_dvd (a.val * c.val) (dvd_mul_left _ _)
    have e₁ := awayLift_comp (A := A (σ a)) (T := Localization.Away a.val)
      (U := Localization.Away (a.val * c.val)) (b (σ a))
      (IsLocalization.Away.awayToAwayRight a.val c.val)
      (IsLocalization.Away.lift_comp a.val _) (hu a) ha
    have e₂ := awayLift_comp (A := A (σ c)) (T := Localization.Away c.val)
      (U := Localization.Away (a.val * c.val)) (b (σ c))
      (IsLocalization.Away.awayToAwayLeft c.val a.val)
      (IsLocalization.Away.lift_comp c.val _) (hu c) hc
    exact (DFunLike.congr_fun e₁ (x (σ a))).trans
      ((hx _ _ _ ha hc).trans (DFunLike.congr_fun e₂ (x (σ c))).symm)
  obtain ⟨r, hr, huniq⟩ :=
    Localization.existsUnique_algebraMap_eq_of_span_eq_top s hb f hf
  have hrx (i : ι) : algebraMap B (A i) r = x i := by
    apply awayLift_injective (T := Localization.Away (b i)) (b i)
    rw [IsLocalization.Away.lift_eq]
    let a : s := ⟨b i, ⟨i, rfl⟩⟩
    exact (hr a).trans (hx (b i) (σ a) i (hu a)
      (IsLocalization.Away.algebraMap_isUnit (b i)))
  refine ⟨r, hrx, ?_⟩
  intro r' hr'
  apply huniq r'
  intro a
  have h := congrArg (IsLocalization.Away.lift (b (σ a)) (hu a) : A (σ a) →+* _)
    (hr' (σ a))
  rw [IsLocalization.Away.lift_eq] at h
  exact h

end SerrePositivity.CommutativeAlgebra.Localization
