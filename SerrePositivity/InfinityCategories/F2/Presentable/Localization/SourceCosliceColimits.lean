module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSource
public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderIso
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer

/-!
概要：固定した元の始域の全 coslice は、元の圏の小余完備性を受け継ぐ。
方針：一点と小さい図式の join を小宇宙で作り、反復 coslice の同型で余極限を戻す。
規約：飽和射の部分圏の余完備性・accessibility はこの補題だけでは主張しない。
使われ方：P-1 f2b、固定始域の presentable 性に向けた余極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C]

/-- 全 coslice の図式は、その展開した元の図式と余極限の存在が同値。 -/
lemma sourceCoslice_hasColimit_iff {K L : SSet.{u + 1}} {p : K ⟶ C}
    (D : L ⟶ sliceUnder p) : HasColimit D ↔ HasColimit (sliceUnderUncurry D) := by
  let e := qCatEquivalenceOfIso (iteratedSliceUnderIso D)
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨e.hom.app _ c, e.map_isInitialVertex hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨e.inv.app _ c, e.symm.map_isInitialVertex hc⟩

/-- 任意の元の小さい固定図式の全 coslice も、小余完備性を受け継ぐ。 -/
lemma smallDiagramCoslice_hasSmallColimits (hC : HasSmallColimits C)
    {K : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    HasSmallColimits (sliceUnder p) := by
  intro L D
  apply (sourceCoslice_hasColimit_iff D).mpr
  let U := sliceUnderUncurry D
  let j := (uliftJoinIso.{u, u + 1} K L).hom
  have hj : IsIso j := inferInstance
  have hr : TrivialKanFibration (sliceUnderRestrict U j) :=
    ⟨MorphismProperty.rlp_of_isIso _ _⟩
  let := hr
  exact (hasColimit_iff_of_trivialRestriction U j).mpr (hC (join K L) (j ≫ U))

/-- 元の圏が全小余極限を持てば、各元の始域の全 coslice も全小余極限を持つ。 -/
lemma sourceCoslice_hasSmallColimits (hC : HasSmallColimits C) (x : C _⦋0⦌) :
    HasSmallColimits (sliceUnder (SSet.yonedaEquiv.symm x)) := by
  intro K D
  apply (sourceCoslice_hasColimit_iff D).mpr
  let U := sliceUnderUncurry D
  let j := (uliftConeShapeIso.{u, u + 1} K 0).hom
  have hj : IsIso j := inferInstance
  have hr : TrivialKanFibration (sliceUnderRestrict U j) :=
    ⟨MorphismProperty.rlp_of_isIso _ _⟩
  let := hr
  exact (hasColimit_iff_of_trivialRestriction U j).mpr
    (hC (join (Δ[0] : SSet.{u}) K) (j ≫ U))

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
