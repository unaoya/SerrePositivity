module

public import SerrePositivity.KST.Comparison.FatDiagonalComparison
public import SerrePositivity.KST.Comparison.FatRealizationHomotopyPullback

/-!
# Segal の realization のホモトピー引き戻しの比較

概要：各面の自然性の四角形がホモトピー引き戻しなら、各行から対角への四角形もそうなる。
方針：有限骨格・無限骨格で証明した fat realization 版を、対角への自然な局所化同型で移す。
規約：Segal 1974 Proposition 1.6 の単体集合の対角版。無限骨格は順序余極限、
模型の比較は自由な退化の収縮という原典と異なる明示した経路を用いる。
使われ方：群状単体的モノイドの bar 束、KST Lemma 2.13 の Segal 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：面の比較を満たす二重単体集合の射で、各行と対角の四角形はホモトピー引き戻し。
方針：fat realization 版と対角の比較の局所化可逆性を四頂点の不変性へ渡す。
規約：Segal 1974 Proposition 1.6。各行の Kan 性は不要で、面の条件は単射だけで十分。
使われ方：bar 束の対角化後のファイバーの比較。
-/
theorem segalRealization_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (hface : ∀ (r k : ℕ) (θ : ⦋r⦌ ⟶ ⦋k⦌), Function.Injective θ →
      IsHomotopyPullback (CommSq.mk (α.naturality θ.op))) (n : ℕ) :
    IsHomotopyPullback (CommSq.mk (diagonalRowEvaluation_naturality α n).symm) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (CommSq.mk (fatRealizationInclusion_map α n))
    (CommSq.mk (diagonalRowEvaluation_naturality α n).symm)
    (𝟙 _) (fatRealizationToDiagonal F) (𝟙 _) (fatRealizationToDiagonal G)
    ?_ (by simp) ?_ ?_ (by infer_instance)
    (fatRealizationToDiagonal_localized_isIso F) (by infer_instance)
    (fatRealizationToDiagonal_localized_isIso G)).mp
    (fatRealizationInclusion_homotopyPullback α hface n)
  · rw [Category.id_comp, fatRealizationInclusion_toDiagonal]
  · exact fatRealizationToDiagonalNatTrans.naturality α
  · rw [Category.id_comp, fatRealizationInclusion_toDiagonal]

end SerrePositivity.KST.Comparison
