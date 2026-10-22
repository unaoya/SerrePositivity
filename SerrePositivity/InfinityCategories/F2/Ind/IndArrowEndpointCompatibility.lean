module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowEndpointFamily

/-!
概要：元の終点 comma の円柱族 F は、元の始点全錐から作る族に厳密に制限される。
方針：C 側の始点評価と、構成した slice 円柱の指定始点を引き戻しの両射影で比較。
規約：全パラメーターの等式。使われ方：元の始点余錐 G と F の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
  (H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)) (V : IndArrowSlicePrism κ D q H)
  (hH : H ≫ diagramConePointRestriction κ D (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)) =
    q ≫ diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

include hH

/-- 元の全始点制限は、同じ始点全錐から作る終点の実引き戻しに一致する。 -/
lemma indArrowEndpointRaw_first : (T ◁ stdSimplex.δ 1) ≫ indArrowEndpointRaw κ D q H V =
    fst T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceEndpointRaw κ D H := by
  apply pullback.hom_ext
  · simp only [Category.assoc, indArrowEndpointRaw_projection,
      indArrowSourceEndpointRaw_projection]
    have hp := congrArg (fun f => f ≫ leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))))) hH
    simp only [Category.assoc, diagramConePointRestriction_projection,
      diagramCommaEvaluation_projection] at hp
    have hp' := congrArg (fun f => fst T (Δ[0] : SSet.{u + 1}) ≫ f) hp.symm
    exact (indArrowOriginalFamily_first κ D q).trans (by simpa only [Category.assoc] using hp')
  · simp only [Category.assoc, indArrowEndpointRaw_slice, indArrowSourceEndpointRaw_slice]
    have he : (T ◁ stdSimplex.δ 1) ≫ (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) =
        (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[0]) ≫ (join T Δ[0] ◁ stdSimplex.δ 1) := by
      rfl
    calc
      _ = (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[0]) ≫
          (join T Δ[0] ◁ stdSimplex.δ 1) ≫ V.val := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ V.val) he
      _ = (joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[0]) ≫
          fst (join T Δ[0]) Δ[0] ≫ indArrowSourceSliceLift κ D H := by rw [V.start]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ indArrowSourceSliceLift κ D H)
          (whiskerRight_fst (joinInl T (Δ[0] : SSet.{u + 1})) (Δ[0] : SSet.{u + 1}))

/-- 元の評価終点に戻しても、F の全始点制限は同じ元の全錐の族に厳密に一致する。 -/
lemma indArrowEndpointFamily_first :
    (T ◁ stdSimplex.δ 1) ≫ indArrowEndpointFamily κ D q H V =
      fst T (Δ[0] : SSet.{u + 1}) ≫ indArrowSourceEndpointFamily κ D H := by
  simpa only [indArrowEndpointFamily, indArrowSourceEndpointFamily, Category.assoc] using
    congrArg (fun f => f ≫ (indArrowEndpointCommaIso κ D).hom)
      (indArrowEndpointRaw_first κ D q H V hH)

/-- 同じ互換性を、元の円柱の零端点包含そのもので回収する。 -/
lemma indArrowEndpointFamily_zero : SSet.ι₀ ≫ indArrowEndpointFamily κ D q H V =
    indArrowSourceEndpointFamily κ D H := by
  let z : T ⟶ T ⊗ (Δ[0] : SSet.{u + 1}) :=
    lift (𝟙 T) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have hz : z ≫ (T ◁ stdSimplex.δ 1) = SSet.ι₀ := by
    dsimp only [z]
    rw [lift_whiskerLeft, stdSimplex.δ_one_eq_const, SSet.comp_const]
    rfl
  have hf : z ≫ fst T (Δ[0] : SSet.{u + 1}) = 𝟙 T := lift_fst _ _
  have h := congrArg (fun f => z ≫ f) (indArrowEndpointFamily_first κ D q H V hH)
  simpa only [← Category.assoc, hz, hf, Category.id_comp] using h

/-- 元の全試験族の C 図式と始点全錐を同時に保つ、終点 comma の円柱族 F が存在。 -/
lemma exists_indArrow_endpoint_family :
    ∃ F : T ⊗ (Δ[1] : SSet.{u + 1}) ⟶ leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))),
      F ≫ leftKanProjection (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)))) =
          indArrowOriginalFamily κ D q ∧
      SSet.ι₀ ≫ F = indArrowSourceEndpointFamily κ D H := by
  obtain ⟨W⟩ := indArrowSlicePrism_nonempty κ D q H hH
  exact ⟨indArrowEndpointFamily κ D q H W, indArrowEndpointFamily_projection κ D q H W,
    indArrowEndpointFamily_zero κ D q H W hH⟩

end SerrePositivity.InfinityCategories.F2.Ind
