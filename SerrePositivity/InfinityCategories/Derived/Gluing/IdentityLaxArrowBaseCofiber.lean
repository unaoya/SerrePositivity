module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityLaxArrowBase
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability
/-!
概要：恒等 lax 圏の矢印による基底同値は、選択 cofiber 差を全関手同型で保つ。
方針：全矢印族の厳密回収に cofiber の制限と完全自然性を合成する。
規約：対角と同じ基底比較を使用。使われ方：恒等比較入力の cone 欄。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] [IsStable X] [IsStable Y]

def identityLaxArrowBaseCofiberComparison (e : QCatEquivalence X Y) : FunctorIso
    ((identityLaxArrowBaseEquivalence e).hom ≫
      CofiberFamily.cofiber Y (F2.laxPullbackArrow (𝟙 Y) (𝟙 Y)))
    (CofiberFamily.cofiber X (F2.laxPullbackArrow (𝟙 X) (𝟙 X)) ≫ e.hom) := by
  letI : IsExactFunctor e.hom := isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have h := CofiberFamily.precompositionIso (F2.laxPullbackArrow (𝟙 Y) (𝟙 Y))
    (identityLaxArrowBaseEquivalence e).hom
  rw [identityLaxArrowBaseEquivalence_arrow] at h
  exact h.trans (CofiberFamily.familyExactComparison e.hom
    (F2.laxPullbackArrow (𝟙 X) (𝟙 X))).symm

end SerrePositivity.InfinityCategories
