module
public import SerrePositivity.KST.NonConnective.DGKappaSplitKAdditivity
public import SerrePositivity.KST.NonConnective.DGSwindleFixedK
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAIntegerNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionUnit

/-!
概要：同じ cone の連結 K の実整数群上で、元の swindle と加法性を消去する。
方針：固定 K の swindle 等式を同じ SOA 比較で戻し、実 cofiber 族の加法性と結ぶ。
規約：D-12 の明示入力を保持し、元の固定 K と別の K を取り替えない。
使われ方：反復懸垂の連結 K 消滅と非連結化の構造射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の固定 K の swindle 等式を、同じ native Perf の連結 BF K 作用へ反映する。 -/
theorem dgKappaSwindleConnectedK_pi (j : ℤ) :
    kHomotopyMap (presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaSwindleSource R D I)) j =
      kHomotopyMap (presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaConeCountableSum R D I)) j := by
  apply MonoidHom.ext
  intro a
  apply (presentedPerfectDGBFSOAGroupEquiv R (dgKappaConeKInput R D I) j).injective
  have hs := presentedPerfectDGBFSOAGroupEquiv_naturality R (dgKappaSwindleInputMap R D I) j a
  have ht := presentedPerfectDGBFSOAGroupEquiv_naturality R (dgKappaCountableInputMap R D I) j a
  exact hs.trans ((DFunLike.congr_fun (dgKappaSwindleFixedK_pi R D I j)
    (presentedPerfectDGBFSOAGroupEquiv R (dgKappaConeKInput R D I) j a)).trans ht.symm)

variable (Z : DGKappaZeroInput R D I)
  (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I), DGKappaSplitCofiberInput R D I X)

include Z H in
/-- D-12 の明示入力の下で、同じ cone の連結 BF K の全整数群の各元は単位元。 -/
theorem dgKappaConnectedK_eq_one (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (presentedPerfectDGStableModel R (DGKappaCone R D I))) j) : a = 1 := by
  have h := dgKappaSplitK_additivity R D I Z H j a
  rw [DFunLike.congr_fun (dgKappaSwindleConnectedK_pi R D I j) a] at h
  have hi : presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
      (DGFunctor.id (A := R) (DGKappaCone R D I)) =
      𝟙 (presentedPerfectDGStableModel R (DGKappaCone R D I)) := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R _ _ _) = 𝟙 _
    rw [presentedPerfectDGAction_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  rw [hi, kHomotopyMap_id, MonoidHom.id_apply] at h
  apply mul_right_cancel
  simpa only [one_mul] using h.symm

include Z H in
/-- 同じ cone の連結 BF K の全整数群は自明。 -/
theorem dgKappaConnectedK_subsingleton (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (presentedPerfectDGStableModel R (DGKappaCone R D I))) j) :=
  ⟨fun a b => (dgKappaConnectedK_eq_one R D I Z H j a).trans
    (dgKappaConnectedK_eq_one R D I Z H j b).symm⟩

include Z H in
/-- 元の同じ固定 dg K 入力の実 BF スペクトルでも、全整数群が自明。 -/
theorem dgKappaFixedK_subsingleton (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgKappaConeKInput R D I)) j) := by
  let e := presentedPerfectDGBFSOAGroupEquiv R (dgKappaConeKInput R D I) j
  have hs := dgKappaConnectedK_subsingleton R D I Z H j
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  exact congrArg e (hs.elim a b)

end SerrePositivity.KST.NonConnective
