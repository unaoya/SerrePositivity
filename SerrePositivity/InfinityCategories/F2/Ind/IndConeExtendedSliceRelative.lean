module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeTensorRelativeExtension
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceCone
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointCommaIso

/-!
概要：元の全 slice 補間データを、終点族の指定変換下で選び直す。
方針：実終点 comma の相対全拡張を取り、同じ初期円柱から再構成する。
規約：初期全円柱・元の q・指定下方余錐 G を変更しない。
使われ方：極大点評価下の実余錐で、旧族上の指定比較を保つ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ初期データを保ち、元の終点族への指定変換を全余錐へ延長できる。
方針：scalar comma の相対補間と旧族固定再構成。
規約：初期データの等号と全終点面の等号。使われ方：元の指定比較の旧族不変性。 -/
lemma exists_indConeExtendedSliceData_relative (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {L C A B : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
    {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
    {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
    (V : IndConeExtendedSliceData κ D q G)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L) (hB : IsKappaSmall κ B)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))))
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ≫
      indConeEndpointRawFace V ≫ (indConeEndpointCommaIso κ D).hom =
      t ≫ sliceUnderProjection z) :
    ∃ (V' : IndConeExtendedSliceData κ D q G) (d : JoinCocone t),
      V'.initial = V.initial ∧
      indConeEndpointRawFace V' ≫ (indConeEndpointCommaIso κ D).hom =
        d.val ≫ sliceUnderProjection z := by
  obtain ⟨E, d, hF, hG, hT⟩ := exists_indComma_coneTensor_relative_extension κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) hA hL hB
    (V.endpoint ≫ (indConeEndpointCommaIso κ D).hom) z t ht
  let E' := E ≫ (indConeEndpointCommaIso κ D).inv
  have hF' : (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E' =
      indConeEndpointRaw V.initial := by
    dsimp only [E']
    rw [← Category.assoc, hF]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using V.endpoint_old
  have hG' : (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E' =
      indConeLowerEndpointRaw V.initial := by
    dsimp only [E']
    rw [← Category.assoc, hG]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using V.endpoint_lower
  obtain ⟨R, hS, hL', hO⟩ := exists_indConeSlice_reconstruction V.initial E' hF' hG'
  let V' : IndConeExtendedSliceData κ D q G := ⟨V.initial, E', R, hF', hG', hS, hL', hO⟩
  refine ⟨V', d, rfl, ?_⟩
  dsimp only [indConeEndpointRawFace, V', E']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hT
end SerrePositivity.InfinityCategories.F2.Ind
