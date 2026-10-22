module

public import SerrePositivity.InfinityCategories.Core.LeftFibrationTerminalFiber

/-!
概要：最後の頂点が終対象である指定単体の上で、点と境界の join を延長する。
方針：指定単体を右の面として貼り、全境界を同じ最後の頂点で充填する。
規約：右の面を定値に制限しない。標的の quasicategory 性は不要。
使われ方：cofinal 性の coslice 引き戻しの相対延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ指定単体の最後の頂点の終対象性は、右の面を保った join の延長を与える。 -/
lemma exists_pointJoinBoundary_extension_over_terminal {X : SSet.{u}} (n : ℕ)
    (b : (Δ[n] : SSet.{u}) ⟶ X)
    (ht : IsTerminalVertex (b.app _ (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (G : join (Δ[0] : SSet.{u}) (boundary n) ⟶ X)
    (hG : joinInr Δ[0] (boundary n : SSet.{u}) ≫ G = (boundary n).ι ≫ b) :
    ∃ H : join (Δ[0] : SSet.{u}) Δ[n] ⟶ X,
      joinMap (𝟙 Δ[0]) (boundary n).ι ≫ H = G ∧ joinInr Δ[0] Δ[n] ≫ H = b := by
  let Z : SSet.{u} := boundary 0
  haveI (A : SSet.{u}) : IsIso (joinInr Z A) := by
    dsimp [Z]
    rw [boundary_zero, ← emptyJoinIso_inv (Δ[0] : SSet.{u}) A]
    infer_instance
  let W : join Z Δ[n] ⟶ X := inv (joinInr Z Δ[n]) ≫ b
  have hW : joinInr Z Δ[n] ≫ W = b := by
    exact IsIso.hom_inv_id_assoc _ _
  have hw : joinMap (boundary 0).ι (𝟙 (boundary n : SSet.{u})) ≫ G =
      joinMap (𝟙 Z) (boundary n).ι ≫ W := by
    apply (cancel_epi (joinInr Z (boundary n : SSet.{u}))).mp
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hG,
      ← Category.assoc, joinInr_joinMap, Category.assoc, hW]
  let hs := (joinUnion_isPushout (boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) (boundary n)).flip
  let T := hs.desc G W hw
  let e := boundaryJoinIso.{u} 0 n
  let v := SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last n))
  let V := v ≫ joinInr Z Δ[n] ≫ joinUnionLeft (boundary 0) (boundary n)
  have hV : V ≫ e.hom = boundaryVertex (0 + n) (Fin.last (0 + n + 1)) := by
    apply (cancel_mono (boundary (0 + n + 1)).ι).mp
    dsimp [V, e]
    simp only [Category.assoc, boundaryJoinIso_hom_ι, boundaryVertex_ι]
    rw [← Category.assoc (joinUnionLeft (boundary 0) (boundary n)), joinUnionLeft_ι,
      ← Category.assoc (joinInr Z Δ[n]), joinInr_joinMap, Category.id_comp]
    exact joinStdSimplexIso_inr_lastVertex n
  have hlast : boundaryVertex (0 + n) (Fin.last (0 + n + 1)) ≫ (e.inv ≫ T) =
      SSet.yonedaEquiv.symm (b.app _ (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    rw [← hV, Category.assoc, Iso.hom_inv_id_assoc]
    dsimp [V, T]
    rw [Category.assoc, Category.assoc, hs.inr_desc, hW]
    exact SSet.yonedaEquiv_symm_comp _ b
  obtain ⟨F, hF⟩ := ht (0 + n) (e.inv ≫ T) hlast
  have hT : (joinUnion (boundary 0) (boundary n)).ι ≫
      ((joinStdSimplexIso 0 n).hom ≫ F) = T := by
    rw [← Category.assoc, ← boundaryJoinIso_hom_ι, Category.assoc, hF,
      Iso.hom_inv_id_assoc]
  refine ⟨(joinStdSimplexIso 0 n).hom ≫ F, ?_, ?_⟩
  · have hh := congrArg (fun t => joinUnionRight (boundary 0) (boundary n) ≫ t) hT
    rw [← Category.assoc, joinUnionRight_ι] at hh
    exact hh.trans (hs.inl_desc G W hw)
  · have hh := congrArg (fun t => joinInr Z Δ[n] ≫
        joinUnionLeft (boundary 0) (boundary n) ≫ t) hT
    rw [← Category.assoc (joinUnionLeft _ _), joinUnionLeft_ι,
      ← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    rw [hs.inr_desc] at hh
    exact hh.trans hW

end SerrePositivity.InfinityCategories.F2.Ind
