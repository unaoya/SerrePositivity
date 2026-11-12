module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedPerfectArrowRefinement
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.SphereLifts
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：元の dg 圏の閉射族による代表加群間の閉射を、実 seed 間の共通提示で精密化する。
方針：係数コードの閉射回収と代表延長の同型を使い、perfect 端点を選択 seed へ戻す。
規約：元の閉射に対応する Yoneda 辺と、その端点輸送を保持する。
使われ方：c′ ゲート3の代表加群の場合。任意 seed 間の加群射には別の係数選択が必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D]
  (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  (a : κ.ord.ToType) {K : Type u} (value : Set.Iio a → D)
  (F : DGFunctor R (c.Objects R κ) (_root_.SerrePositivity.InfinityCategories.DGObjectImage value))
  (source target : K → Set.Iio a)
  (f : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
    ForgetEnrichment.of (Complex R) (value (target k)))
  (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ)

local notation "code" => dgClosedFamilySourceCode R κ c a D value F source target f hκ hK
local notation "C" => (DGCategoryPresentationCode.Objects R κ code)
local notation "L" => dgClosedFamilySourceEvaluation R κ c a D value F source target f hκ hK
local notation "g" => dgClosedFamilySourceArrow R κ c a D value F source target f hκ hK

include c F hκ hK

lemma dgKappaPresentedRepresentableArrowRefinement (h0 : κ ≠ 0) (k : K) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ ((dgYoneda R D).onClosed.map (f k))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedClosedArrowRefinement_of_perfect_source R D κ h0 code L
    (ForgetEnrichment.of (Complex R) (representable R (D := C) (source k)))
    (ForgetEnrichment.of (Complex R) (representable R (D := C) (target k)))
    (representable_homotopicallyProjective R C (source k))
    (representable_homotopicallyProjective R C (target k))
    (modulePerfectOver_representable R C (source k) (Set.mem_univ _))
    (modulePerfectOver_representable R C (target k) (Set.mem_univ _))
    ((dgYoneda R C).onClosed.map (g k)) _
    ((moduleToHomotopy R D).mapIso (dgModuleExtensionRepresentableIso R C D L (source k)))
    ((moduleToHomotopy R D).mapIso (dgModuleExtensionRepresentableIso R C D L (target k)))
  change (moduleToHomotopy R D).map _ ≫ (moduleToHomotopy R D).map _ =
    (moduleToHomotopy R D).map _ ≫ (moduleToHomotopy R D).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (moduleToHomotopy R D).map
    (dgClosedFamilySourceRepresentableArrow_comm R κ c a D value F source target f hκ hK k)

lemma dgKappaPresentedRepresentableModuleArrowRefinement
    (h0 : κ ≠ 0)
    (fM : ∀ k, ForgetEnrichment.of (Complex R) (representable R (value (source k))) ⟶
      ForgetEnrichment.of (Complex R) (representable R (value (target k)))) (k : K) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ (fM k)) := by
  let Y := dgYoneda R D
  have hY : ∀ x y, IsIso (Y.map x y) := by
    intro x y
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  letI : Y.onClosed.Full := Y.onClosed_full_of_homIso hY
  let inputArrow : ∀ k, ForgetEnrichment.of (Complex R) (value (source k)) ⟶
      ForgetEnrichment.of (Complex R) (value (target k)) :=
    fun k => Y.onClosed.preimage (fM k)
  have hg (k : K) : Y.onClosed.map (inputArrow k) = fM k :=
    Y.onClosed.map_preimage (fM k)
  have h := dgKappaPresentedRepresentableArrowRefinement R D κ c a value F
    source target inputArrow hκ hK h0 k
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedClosedArrowRefinement R D κ (Y.onClosed.map (inputArrow k))) at h
  rw [hg] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
