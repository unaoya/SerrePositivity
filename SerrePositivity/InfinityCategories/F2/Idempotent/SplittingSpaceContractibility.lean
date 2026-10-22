module

public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingSpace
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrongSplittingLimitExistence

/-!
概要：指定した元の全 Idem 図式が強い分裂を持てば、その全分裂空間は可縮 Kan 複体。
方針：正次の境界は元の充満忠実な inner 制限で充填し、零次は元の厳密な分裂を使う。
規約：全次数で元の全 Idem 図式を固定する。標的全体の冪等完備性は要求しない。
使われ方：HTT 4.4.5.16 の coherent な強い分裂の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 指定した元の全 Idem 図式の全強分裂空間は、一つの厳密な分裂から可縮 Kan となる。 -/
lemma strongSplittingSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {d : CoherentIdempotent X} (s : StrongSplitting d) :
    IsContractibleKan (strongSplittingSpace d) := by
  intro n a
  cases n with
  | zero => exact ⟨SSet.yonedaEquiv.symm (strongSplittingSpaceVertex s), boundary.hom_ext₀⟩
  | succ n =>
    let p := strongSplittingRestriction X
    let b := functorVertex d
    have : HasLiftingProperty (boundary (n + 1)).ι p :=
      (strongSplittingRestriction_isFullyFaithful X).hasLiftingProperty_boundary_succ n
    have sq : CommSq (a ≫ vertexFiberι p b) (boundary (n + 1)).ι p (SSet.const b) := by
      constructor
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
    refine ⟨vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι]
    exact sq.fac_left

/-- 指定した元の全 Idem 図式の余極限から、同じ全分裂空間の可縮 Kan 性を得る。 -/
lemma strongSplittingSpace_isContractibleKan_of_hasColimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasColimit d) :
    IsContractibleKan (strongSplittingSpace d) := by
  obtain ⟨s⟩ := strongSplitting_exists_of_hasColimit d hd
  exact strongSplittingSpace_isContractibleKan s

/-- 指定した元の全 Idem 図式の極限からも、同じ全分裂空間の可縮 Kan 性を得る。 -/
lemma strongSplittingSpace_isContractibleKan_of_hasLimit {X : SSet.{u}} [Quasicategory X]
    (d : CoherentIdempotent X) (hd : HasLimit d) :
    IsContractibleKan (strongSplittingSpace d) := by
  obtain ⟨s⟩ := strongSplitting_exists_of_hasLimit d hd
  exact strongSplittingSpace_isContractibleKan s

end SerrePositivity.InfinityCategories.F2.Idempotent
