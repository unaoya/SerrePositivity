module

public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfFinalHornFixedEdge
public import SerrePositivity.InfinityCategories.ModelBridge.QuillenCfFinalHornBase

/-!
# 元の右 Quillen 候補辺の相対ホーンからの Hom 構成

概要：実際の固定最終辺と回収射を照合し、元の相対ホーンへ Hom 持ち上げを適用する。
方針：既知面の自然性・通常の射の抽出・区間の単調性を使う。
規約：ambient の全対象に Hom 条件を仮定せず、元の下段始域について証明する。
使われ方：HTT 5.2.4.6 の Cartesian な持ち上げの構成。豊穣単体の復元は別途必要。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  {n : ℕ} (R : EnrichedFunctor SSet.{u} D C)
variable {L : C ⥤ D} (adj : L ⊣ coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [FixedSimplicialPushoutProduct SC.tensor] [FixedSimplicialPushoutProduct SD.tensor]

include SC SD in
/-- 元の右 Quillen 候補辺を固定した相対ホーンから、二つの未知 Hom を全既知面を保持して構成する。 -/
lemma quillenCfFinalHornRight_relative_unknownHom_extension
    (τQ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, Fin.last (n + 2)]).ι (quillenCfCollageProjection R) β)
    (Y : CofibrantFibrantObjects D)
    (hedge : τQ.app (Opposite.op ⦋1⦌) (finalHornEdge n) =
      (quillenCfRightLiftEdge R adj cofC Y).edge) :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (hornObj τQ 0) (hornObj τQ (Fin.last (n + 2))),
      (∀ (j : Fin (n + 3)) (hj0 : 0 < j) (hjn : j < Fin.last (n + 2)),
        (pathAvoids (ULift.up j)).ι ≫ g = hornInnerZeroHom τQ j (ne_of_lt hjn) hj0 hjn) ∧
      (∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
        (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom τQ b hb0 hbp) ∧
      ∃ f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
        (ULift.up (finalHornPenultimate n))) ⟶
          SimplicialCategory.sHom (hornObj τQ 0) (hornObj τQ (finalHornPenultimate n)),
        (∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom τQ j) ∧
        f ≫ eHomWhiskerLeft SSet (hornObj τQ 0) (finalHornLastArrow τQ) =
          finalHornAppend n ≫ g := by
  obtain ⟨X, hzero⟩ := quillenCfFinalHorn_prefix_bottom R τQ β sq
    (quillenCfRightLiftObject R adj cofC Y) Y (quillenCfRightLiftArrow R adj cofC Y)
    hedge 0 (Fin.zero_le _)
  exact quillenCfFinalHornRight_unknownHom_extension R adj cofC SC SD τQ X Y hzero hedge

end
end SerrePositivity.InfinityCategories.HomotopyLimits
