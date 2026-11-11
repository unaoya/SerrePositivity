module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.NativeTarget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ChoiceInvariant

/-!
概要：固定 data の全頂点を使う厳密豊穣経路が要求する単位等号を明示する。
方針：native 単位射の零単体を評価し、ε core の頂点から実分解関手を回収する。
規約：この必要条件の成立・不成立、また一般の map の不存在は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory MonoidalCategory DifferentialGraded KST.NonConnective KST.SConstruction
open DGCategoryCellResolution
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
local notation "IA" => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R A κ hκ
local notation "CA" => DGKappaCone R A IA
local notation "PA" => Source R CA
local notation "SA" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R CA (dgKappaConePerfectObjects R A IA)

/-- 固定頂点で厳密に単位を保つなら、固定恒等 data の実分解関手自体が恒等となる。 -/
lemma dgSuspensionResolved_identity_of_nativeUnit
    (H : dgFunctorNativeMappingSpace R A A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A A)
    (hH : H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A A (DGFunctor.id A)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A A (𝟙 A))
    (hu : dgFunctorNativeIdentity R A ≫ H = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonUnit R κ hκ A) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).resolved = DGFunctor.id PA := by
  have he := congrArg (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A A)) hu
  change H.app (Opposite.op ⦋0⦌)
    ((dgFunctorNativeIdentity R A).app _ PUnit.unit) =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonUnit R κ hκ A).app _ PUnit.unit at he
  have hs : (dgFunctorNativeIdentity R A).app (Opposite.op ⦋0⦌) PUnit.unit =
      dgFunctorNativeMappingVertex R A A (DGFunctor.id A) :=
    (SSet.unitHomEquiv (dgFunctorNativeMappingSpace R A A)).apply_symm_apply
      (dgFunctorNativeMappingVertex R A A (DGFunctor.id A))
  have ht : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonUnit R κ hκ A).app
      (Opposite.op ⦋0⦌) PUnit.unit =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonNativeVertex R PA PA SA SA (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonUnitObject R PA SA) :=
    (SSet.unitHomEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A A)).apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.quotientEpsilonNativeVertex R PA PA SA SA (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonUnitObject R PA SA))
  rw [hs, ht] at he
  change H.app _ (dgFunctorNativeMappingVertex R A A (DGFunctor.id A)) = _ at he
  rw [hH] at he
  exact congrArg _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε.val (congrArg (fun z => z.val.obj 0) he)

/-- この厳密単位条件は、cone の恒等入力で代表を動かさないことも要求する。 -/
lemma dgSuspensionCone_obj_identity_of_nativeUnit
    (H : dgFunctorNativeMappingSpace R A A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A A)
    (hH : H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A A (DGFunctor.id A)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A A (𝟙 A))
    (hu : dgFunctorNativeIdentity R A ≫ H = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonUnit R κ hκ A)
    (M : CA) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone.obj M = M := by
  have h := dgSuspensionResolved_identity_of_nativeUnit R κ hκ A H hH hu
  exact congrArg (fun F => (F.obj (⟨M⟩ : PA)).val) h

/-- 固定恒等 data の対象選択は、入力 cone の同型な二代表を同じ対象に送る。 -/
lemma dgSuspensionCone_identity_obj_eq_of_iso (M N : CA) (a : M.val ≅ N.val) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone.obj M =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone.obj N := by
  letI : Nonempty κ.ord.ToType :=
    Cardinal.nonempty_ord_toType (ne_of_gt (lt_trans Cardinal.aleph0_pos hκ))
  letI : CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
      (dgModuleExtension R A A (DGFunctor.id A)).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R A A (DGFunctor.id A)).leftAdjoint_preservesColimits
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgProjectiveClosureFunctor_obj_eq_of_sourceIso
    (R := R) (C := A) (D := A) (F := dgModuleExtension R A A (DGFunctor.id A))
    (hO := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kappaOrdinal_countable_strict_bound hκ Fact.out)
    (B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R A κ) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureBaseFamily R A κ)
    (hBF := fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R (DGFunctor.id A) i,
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereFreeExtensionIso R A A (DGFunctor.id A) i⟩⟩) M N a

/-- 固定 data 自体の resolved 恒等性は、cone の各対象を動かさないことを要求する。 -/
lemma dgSuspensionCone_obj_eq_of_resolvedIdentity
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).resolved = DGFunctor.id PA)
    (M : CA) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).cone.obj M = M :=
  congrArg (fun F => (F.obj (⟨M⟩ : PA)).val) h

/-- 固定 data の resolved 恒等性そのものが、cone 代表集合の実同型に関する骨格性を要求する。 -/
lemma dgSuspensionCone_eq_of_iso_of_resolvedIdentity
    (h : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionUnconditionalMapData R κ hκ (𝟙 A)).resolved = DGFunctor.id PA)
    (M N : CA) (a : M.val ≅ N.val) : M = N :=
  (dgSuspensionCone_obj_eq_of_resolvedIdentity R κ hκ A h M).symm.trans
    ((dgSuspensionCone_identity_obj_eq_of_iso R κ hκ A M N a).trans
      (dgSuspensionCone_obj_eq_of_resolvedIdentity R κ hκ A h N))

/-- 固定 data の厳密単位経路は、元の cone 代表集合の同型に関する骨格性を要求する。 -/
lemma dgSuspensionCone_eq_of_iso_of_nativeUnit
    (H : dgFunctorNativeMappingSpace R A A ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonCore R κ hκ A A)
    (hH : H.app (Opposite.op ⦋0⦌) (dgFunctorNativeMappingVertex R A A (DGFunctor.id A)) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonVertex R κ hκ A A (𝟙 A))
    (hu : dgFunctorNativeIdentity R A ≫ H = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgSuspensionResolvedEpsilonUnit R κ hκ A)
    (M N : CA) (a : M.val ≅ N.val) : M = N :=
  (dgSuspensionCone_obj_identity_of_nativeUnit R κ hκ A H hH hu M).symm.trans
    ((dgSuspensionCone_identity_obj_eq_of_iso R κ hκ A M N a).trans
      (dgSuspensionCone_obj_identity_of_nativeUnit R κ hκ A H hH hu N))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
