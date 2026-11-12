module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallWeightedSectionsContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetNerve
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan

/-!
概要：小さい poset 上の Bousfield–Kan の元の極限模型は μ-filtered な通常の余極限を保つ。
方針：各 Over の対象を元の poset に埋め込み、同じ重みの小ささを証明して end の連続性を使う。
規約：元の bousfieldKanHolimFunctor を使う。native な Space の全錐の極限性の移送は別途必要。
使われ方：小さい部分余極限の μ-compact 性のための交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
include h hI

/-- 元の小さい poset の各 Bousfield–Kan 重みの全非退化単体も同じ μ 未満。 -/
lemma bousfieldKanWeight_poset_isKappaSmall (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj i) := by
  have hOver : HasCardinalLT (Over i) μ := hI.of_injective (fun x ↦ x.left) (by
    intro x y hxy
    exact CostructuredArrow.obj_ext x y hxy (by subsingleton))
  have : Quiver.IsThin (Over i) := fun _ _ ↦
    ⟨fun _ _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _)⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_nerve_of_cardinalChangeBound h (Over i) hOver

/-- 同じ小さい poset の元の Bousfield–Kan 極限模型は μ-filtered strict 余極限を保つ。 -/
lemma bousfieldKanHolimFunctor_poset_preservesCardinalFilteredColimits
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ] :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolimFunctor I) := by
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hArrow : HasCardinalLT (Arrow I) μ :=
    (hasCardinalLT_arrow_iff_of_isThin I μ hμ.le).mpr hI
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.weightedSectionsFunctor_preservesCardinalFilteredColimits hμ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (bousfieldKanWeight_poset_isKappaSmall h I hI) J hArrow

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
