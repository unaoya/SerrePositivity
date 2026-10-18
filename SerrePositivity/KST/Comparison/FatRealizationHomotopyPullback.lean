module

public import SerrePositivity.KST.Comparison.ActualSequentialComparison
public import SerrePositivity.KST.Comparison.FatSkeletonTail
public import SerrePositivity.KST.Comparison.FatSkeletonGeneralComparison

/-!
# fat realization 全体への各行のホモトピー引き戻し

概要：面の比較を満たす二重単体集合の射で、各行から全体への比較を証明する。
方針：各行を含む骨格の尾を使い、有限骨格の四角形を実際の順序余極限へ移す。
規約：Segal 1974 Proposition 1.6 の fat realization 版。無限骨格の段階は
原典の telescope と異なり、有限表示可能性と厳密な引き戻しの余極限で証明する。
使われ方：fat realization と対角の比較を介した bar 束の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：面のホモトピー引き戻し性から、各行と fat realization 全体の四角形を得る。
方針：小さい行を含む全骨格の比較を、単射な順序余極限の定理で移す。
規約：各行の Kan 性は不要。対角への比較は結論に含めない。
使われ方：Segal Proposition 1.6 の対角版への最後の模型の比較。
-/
theorem fatRealizationInclusion_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hface : ∀ (r k : ℕ) (θ : ⦋r⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op))) (m : ℕ) :
    IsHomotopyPullback (CommSq.mk (fatRealizationInclusion_map α m)) := by
  let sq := CommSq.mk (fatSkeletonTailRow_map α m)
  apply actual_sequential_homotopyPullback sq ?_ ?_ ?_
    (constCocone ℕ (F.obj (op ⦋m⦌) ⊗ Δ[m])) (fatSkeletonTailCocone F m)
    (constCocone ℕ (G.obj (op ⦋m⦌) ⊗ Δ[m])) (fatSkeletonTailCocone G m)
    (isColimitConstCocone ℕ _) (fatSkeletonTailCoconeIsColimit F m)
    (isColimitConstCocone ℕ _) (fatSkeletonTailCoconeIsColimit G m)
    (CommSq.mk (fatRealizationInclusion_map α m)) ?_ ?_ ?_ ?_
  · intro n
    change Mono (𝟙 (F.obj (op ⦋m⦌) ⊗ Δ[m]))
    infer_instance
  · intro n
    change Mono (SSet.Subcomplex.homOfLE (fatSkeleton_monotone F
      (show m + n ≤ m + (n + 1) by omega)))
    infer_instance
  · intro n
    exact fatSkeletonRow_general_homotopyPullback α hface (m + n) m (Nat.le_add_right m n)
  · intro n
    change (𝟙 _) ≫ fatRealizationInclusion F m =
      fatSkeletonRowOfLE F (Nat.le_add_right m n) ≫ (fatSkeleton F (m + n)).ι
    rw [Category.id_comp, fatSkeletonRowOfLE_ι]
  · intro n
    change (𝟙 _) ≫ (α.app (op ⦋m⦌) ▷ Δ[m]) =
      (α.app (op ⦋m⦌) ▷ Δ[m]) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  · intro n
    exact (fatSkeletonMap_ι α (m + n)).symm
  · intro n
    change (𝟙 _) ≫ fatRealizationInclusion G m =
      fatSkeletonRowOfLE G (Nat.le_add_right m n) ≫ (fatSkeleton G (m + n)).ι
    rw [Category.id_comp, fatSkeletonRowOfLE_ι]

end SerrePositivity.KST.Comparison
