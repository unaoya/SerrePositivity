module
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberExact
public import SerrePositivity.KST.NonConnective.ConnectedKMiddleAdditivity

/-!
概要：元の cone の実分裂 cofiber 族へ、連結 BF K の整数次数の加法性を適用する。
方針：同じ完全関手の三評価を元の dg 作用に同定し、既存の K 加法性を前合成する。
規約：D-12 の明示入力を保持し、非連結 K の局所化性を仮定しない。
使われ方：id ⊕ T と T の同じ K 作用を消去する swindle。
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
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)
  (H : ∀ X : PresentedPerfectDGObject R (DGKappaCone R D I), DGKappaSplitCofiberInput R D I X)

/-- 完全 cofiber 族の subobject は、元の恒等 dg 入力の作用そのもの。 -/
theorem dgKappaSplitCofiberStableMap_subobject :
    dgKappaSplitCofiberStableMap R D I Z H ≫
        cofiberStableSubobject (presentedPerfectDGStableModel R (DGKappaCone R D I)) =
      presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (DGFunctor.id (A := R) (DGKappaCone R D I)) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm.trans (dgKappaSplitCofiberFamily_subobject R D I Z H)

/-- 完全 cofiber 族の middle は、元の id ⊕ T の作用そのもの。 -/
theorem dgKappaSplitCofiberStableMap_middle :
    dgKappaSplitCofiberStableMap R D I Z H ≫
        cofiberStableMiddle (presentedPerfectDGStableModel R (DGKappaCone R D I)) =
      presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaSwindleSource R D I) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm.trans (dgKappaSplitCofiberFamily_middle R D I Z H)

/-- 完全 cofiber 族の quotient は、元の可算和 T の作用そのもの。 -/
theorem dgKappaSplitCofiberStableMap_quotient :
    dgKappaSplitCofiberStableMap R D I Z H ≫
        cofiberStableQuotient (presentedPerfectDGStableModel R (DGKappaCone R D I)) =
      presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaConeCountableSum R D I) := by
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm.trans (dgKappaSplitCofiberFamily_quotient R D I Z H)

include Z H in
/-- 元の同じ cone の連結 BF K 上で、id ⊕ T の全整数作用は id 作用と T 作用の積。 -/
theorem dgKappaSplitK_additivity (j : ℤ)
    (a : OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (presentedPerfectDGStableModel R (DGKappaCone R D I))) j) :
    kHomotopyMap (presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaSwindleSource R D I)) j a =
      kHomotopyMap (presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
          (DGFunctor.id (A := R) (DGKappaCone R D I))) j a *
        kHomotopyMap (presentedPerfectDGActionStableMap R (DGKappaCone R D I) (DGKappaCone R D I)
          (dgKappaConeCountableSum R D I)) j a := by
  let M := presentedPerfectDGStableModel R (DGKappaCone R D I)
  let f := dgKappaSplitCofiberStableMap R D I Z H
  have h := connectedKMiddle_additivity M j (kHomotopyMap f j a)
  have hs := congrArg (fun g => kHomotopyMap g j a)
    (dgKappaSplitCofiberStableMap_subobject R D I Z H)
  have hm := congrArg (fun g => kHomotopyMap g j a)
    (dgKappaSplitCofiberStableMap_middle R D I Z H)
  have hq := congrArg (fun g => kHomotopyMap g j a)
    (dgKappaSplitCofiberStableMap_quotient R D I Z H)
  simp only [kHomotopyMap_comp, MonoidHom.comp_apply] at hs hm hq
  exact hm.symm.trans (h.trans (congrArg₂ (· * ·) hs hq))

end SerrePositivity.KST.NonConnective
