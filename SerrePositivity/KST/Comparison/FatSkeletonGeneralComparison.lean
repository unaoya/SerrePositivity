module

public import SerrePositivity.KST.Comparison.FatSkeletonHomotopyPullback
public import SerrePositivity.KST.Comparison.FatSkeletonInvariance

/-!
# Kan 性を仮定しない有限骨格の行の比較

概要：面のホモトピー引き戻し性だけから、各行の有限骨格への比較を得る。
方針：各行の関手的な Kan 分解と有限骨格の局所化不変性で、Kan の場合から移す。
規約：Segal 1974 Proposition 1.6 の有限骨格部分。
使われ方：一般の二重単体集合の射の無限骨格への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：面の比較を満たす任意の射で、各行から有限骨格への四角形はホモトピー引き戻し。
方針：各行の Kan 分解の単位を、行の積と骨格の双方で局所化同型として比較する。
規約：各行の Kan 性は仮定しない。結論は全ての m ≤ n を含む。
使われ方：Segal Proposition 1.6 の無限骨格の段階への入力。
-/
theorem fatSkeletonRow_general_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hface : ∀ (m k : ℕ) (θ : ⦋m⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op)))
    (n m : ℕ) (hm : m ≤ n) :
    IsHomotopyPullback (CommSq.mk (fatSkeletonRowOfLE_map α hm)) := by
  let β := diagramKanProjection α
  let i := diagramKanUnit α
  have hi : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (i.app (op ⦋k⦌))) := fun k =>
    Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
      (diagramKanUnit_anodyne α _)
  have hβface : ∀ (r k : ℕ) (θ : ⦋r⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (β.naturality θ.op)) := by
    intro r k θ hθ
    exact (diagramKan_arrowSquare_iff α θ.op).mp (hface r k θ hθ)
  have hβ := fatSkeletonRow_homotopyPullback β
    (fun k => diagramKanProjection_rlp α (op ⦋k⦌)) hβface n m hm
  have hfac : i.app (op ⦋m⦌) ≫ β.app (op ⦋m⦌) = α.app (op ⦋m⦌) :=
    congrArg (fun t => t.app (op ⦋m⦌)) (diagramKan_fac α)
  have hskel : fatSkeletonMap i n ≫ fatSkeletonMap β n = fatSkeletonMap α n := by
    change (fatSkeletonFunctor n).map i ≫ (fatSkeletonFunctor n).map β = _
    rw [← Functor.map_comp]
    exact congrArg (fun t => (fatSkeletonFunctor n).map t) (diagramKan_fac α)
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk (fatSkeletonRowOfLE_map α hm)) (CommSq.mk (fatSkeletonRowOfLE_map β hm))
    (i.app (op ⦋m⦌) ▷ Δ[m]) (fatSkeletonMap i n) (𝟙 _) (𝟙 _)
    (fatSkeletonRowOfLE_map i hm) ?_ ?_ (by simp)
    (AnodyneHomotopy.whiskerRight_anodyneQ_isIso _ (hi m) Δ[m])
    (fatSkeletonMap_localized_isIso i hi n) (by infer_instance) (by infer_instance)).mpr hβ
  · rw [Category.comp_id, ← comp_whiskerRight, hfac]
  · rw [Category.comp_id, hskel]

end SerrePositivity.KST.Comparison
