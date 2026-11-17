module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveRecovery
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveRetraction

/-!
概要：Grothendieck射列とprefix重み付きnerveの、同じ底上の厳密な同型。
方針：既存の前向き全写像の各次数の両往復から、その同じ写像を可逆にする。
規約：IS-W2 R03e。新しい逆写像の自然性を仮定しない。
使われ方：要素圏のnerveと同じ重み付きnerveの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元の前向き写像は、各次数で同じ逆射列を逆に持つ全単射。 -/
theorem grothWeightedNerveForward_bijective (n : ℕ) :
    Function.Bijective (grothWeightedNerveSimplex F (n := n)) :=
  ⟨Function.LeftInverse.injective (grothWeightedNerveInverseSimplex_forward F),
    Function.RightInverse.surjective (grothWeightedNerveSimplex_inverse F)⟩

/-- 元の前向き全写像を前向きとする、単体集合の同型。 -/
def grothendieckWeightedNerveIso : nerve (Grothendieck F) ≅ weightedNerve (F ⋙ nerveFunctor) := by
  letI : ∀ k, IsIso ((grothWeightedNerveForward F).app k) := fun k =>
    (CategoryTheory.isIso_iff_bijective _).mpr (grothWeightedNerveForward_bijective F k.unop.len)
  letI : IsIso (grothWeightedNerveForward F) :=
    (NatTrans.isIso_iff_isIso_app _).mpr (fun _ => inferInstance)
  exact asIso (grothWeightedNerveForward F)

/-- 全同型の前向き写像は、同じ基底への射影を厳密に保つ。 -/
theorem grothendieckWeightedNerveIso_projection :
    (grothendieckWeightedNerveIso F).hom ≫ weightedNerveProjection (F ⋙ nerveFunctor) =
      nerveMap (Grothendieck.forget F) := by
  simpa only [grothendieckWeightedNerveIso, asIso_hom] using
    grothWeightedNerveForward_projection F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
