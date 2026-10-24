module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNativeAllBoundaryCylinder
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeJoinCylinderOverExtension
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEvaluationLifting
/-!
概要：元の両全余錐を、指定始点評価を保つ join 可逆円柱へ延長する。
方針：元の全円柱の両端と評価の固定条件を、そのまま実際の射で回収する。
規約：標的の固定 fiber の充填性を追加仮定にしない。
使われ方：指定始点評価の下での全余錐比較の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex (liftedIntervalToSmall ≫ D)) ≫
  arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "b" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) T) ≫
  indArrowOriginalFamily κ D q ≫ indYoneda κ C) ≫
    arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "s" => SSet.ι₀ ≫ indArrowNormalizedPrism κ D q
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)
local notation "f" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) (join T Δ[0])) ≫ r) ≫
  arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "g" => joinMap q (𝟙 Δ[0]) ≫ Subtype.val (diagramCommaCocone κ D)
/-- 概要：原の両余錐を両端に持ち、元の始点評価を保つ join 可逆円柱。
方針：同じ相対延長を適用。規約：両端と指定全評価を保持。使われ方：slice 内の相対反映。 -/
lemma exists_indArrowSourceFixedJoinCylinder :
    ∃ F : join (T ⊗ equivalenceInterval) (Δ[0] : SSet.{u + 1}) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}))).obj (IndInfinity κ C),
    joinMap (equivalenceCylinderEndpoint T false) (𝟙 Δ[0]) ≫ F = f ∧
    joinMap (equivalenceCylinderEndpoint T true) (𝟙 Δ[0]) ≫ F = g ∧
    F ≫ e = joinMap (fst T equivalenceInterval) (𝟙 Δ[0]) ≫ s ∧
    joinInr (T ⊗ equivalenceInterval) Δ[0] ≫ F = p := by
  obtain ⟨U, h₀, h₁, _, hTip, hEval⟩ := exists_indArrowNativeAllBoundaryCylinder W
  have ht (flag : Bool) : joinInr T Δ[0] ≫
      (equivalenceCylinderEndpoint (join T Δ[0]) flag ≫ U) = p := by
    rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
      hTip, ← Category.assoc, equivalenceCylinderEndpoint_fst, Category.id_comp]
  have hf : joinInr T Δ[0] ≫ f = p := by rw [← h₀]; exact ht false
  have hg : joinInr T Δ[0] ≫ g = p := by rw [← h₁]; exact ht true
  have he : f ≫ e = s := by
    rw [← h₀, Category.assoc, hEval, ← Category.assoc,
      equivalenceCylinderEndpoint_fst, Category.id_comp]
  obtain ⟨F, hF₀, hF₁, hFp⟩ := exists_joinCylinder_extension_of_equivalenceFamily_over
    e (kanEquivalenceLifting_evaluateFunctorAt _) f g (hf.trans hg.symm) U h₀ h₁
    (by rw [hf]; exact hTip) (by rw [he]; exact hEval)
  refine ⟨F, hF₀, hF₁, ?_, ?_⟩
  · rw [he] at hFp
    exact hFp
  · have h := congrArg (fun k => joinInr T (Δ[0] : SSet.{u + 1}) ≫ k) hF₀
    simp only [← Category.assoc, joinInr_joinMap, Category.id_comp] at h
    have hh : joinInr (T ⊗ equivalenceInterval) Δ[0] ≫ F = joinInr T Δ[0] ≫ f := by
      convert h using 1
      rfl
    exact hh.trans hf
end SerrePositivity.InfinityCategories.F2.Ind
