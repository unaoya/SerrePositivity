module
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
public import SerrePositivity.KST.LocalizingInvariants.LocalizationEssentialSurjectivity

/-! # Verdier 商の元の対象と完全関手による三角圏 K₀ の全射性

零次の対象類の計算であり、全写像空間の比較や K の局所化性を仮定しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 完全関手の元の三角圏 Grothendieck 群への作用。 -/
def stableKZeroMap {X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap X Y) :
    TriangulatedK0 (hoFunctor.obj X.obj) →+ TriangulatedK0 (hoFunctor.obj Y.obj) :=
  TriangulatedK0.map (hoFunctor.map F.hom).toFunctor

/-- 各対象が像と同型なら、同じ元の完全関手の三角圏 K₀ への作用は全射。 -/
theorem stableKZeroMap_surjective_of_essentiallySurjective
    {X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap X Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective F.hom) :
    Function.Surjective (stableKZeroMap F) := by
  let M := stableKZeroMap F
  have hg : ∀ a : hoFunctor.obj Y.obj, TriangulatedK0.mk a ∈ M.range := by
    intro a
    obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨x, ⟨e⟩⟩ := hF y
    refine ⟨TriangulatedK0.mk (C := hoFunctor.obj X.obj) (HomotopyCategory.mk x), ?_⟩
    change TriangulatedK0.map (hoFunctor.map F.hom).toFunctor
      (TriangulatedK0.mk (C := hoFunctor.obj X.obj) (HomotopyCategory.mk x)) =
        TriangulatedK0.mk (C := hoFunctor.obj Y.obj) (HomotopyCategory.mk y)
    exact (TriangulatedK0.map_mk (C := hoFunctor.obj X.obj) (D := hoFunctor.obj Y.obj)
      (hoFunctor.map F.hom).toFunctor (HomotopyCategory.mk x)).trans
        (TriangulatedK0.mk_iso e)
  intro a
  change a ∈ M.range
  refine QuotientAddGroup.induction_on a ?_
  intro b
  induction b using FreeAbelianGroup.induction_on with
  | zero => exact M.range.zero_mem
  | of y => exact hg y
  | neg y hy =>
      simpa only [QuotientAddGroup.mk_neg] using M.range.neg_mem hy
  | add b c hb hc =>
      simpa only [QuotientAddGroup.mk_add] using M.range.add_mem hb hc

/-- 元の Verdier 商射は、同じ三角圏 K₀ の実準同型で全射。 -/
theorem verdierKZeroMap_surjective {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    Function.Surjective (stableKZeroMap q) :=
  stableKZeroMap_surjective_of_essentiallySurjective q
    (localization_isEssentiallySurjective q.hom _ h.quotient)

end SerrePositivity.KST.Fibration
