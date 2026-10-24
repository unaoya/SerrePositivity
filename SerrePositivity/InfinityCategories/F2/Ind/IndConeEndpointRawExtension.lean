module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTensorNativeExtension
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointCommaIso
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointRawBoundary

/-!
概要：元の q と指定下方余錐 G の同じ実終点 comma 内の全族を、元の全余錐積へ延長する。
方針：指定終点の標準 scalar comma で拡張し、同じ表示変更の逆で戻す。
規約：元の両全族と全共有境界を厳密に保持し、κ の正則性以外を追加しない。
使われ方：旧族を固定する相対再構成へ実際の終点補間を渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の q と指定 G の実終点族には、両全境界を保つ同じ積上の拡張が存在。
方針：同じ scalar comma の実拡張を移送。規約：元の全射。使われ方：全族の再構成。 -/
lemma exists_indConeEndpointRaw_extension (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {A L C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u}))))
    (V : IndConeSliceInterpolationData κ D q G)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) :
    ∃ E : join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
      pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)),
      (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E = indConeEndpointRaw V ∧
      (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E =
          indConeLowerEndpointRaw V := by
  let e := indConeEndpointCommaIso κ D
  have h : ((SSet.uliftFunctor.{u + 1, u}).obj A ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      (indConeEndpointRaw V ≫ e.hom) =
    (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ (indConeLowerEndpointRaw V ≫ e.hom) := by
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ e.hom) (indConeEndpointRaw_boundary V)
  obtain ⟨E, hF, hG⟩ := exists_indComma_coneTensor_native_extension κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) hA hL
    (indConeEndpointRaw V ≫ e.hom) (indConeLowerEndpointRaw V ≫ e.hom) h
  refine ⟨E ≫ e.inv, ?_, ?_⟩
  · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ e.inv) hF
  · simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ e.inv) hG
end SerrePositivity.InfinityCategories.F2.Ind
