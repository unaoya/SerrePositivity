module

public import SerrePositivity.KST.Comparison.SpanCylinderColimitNaturality
public import SerrePositivity.KST.Comparison.SpanGluing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 単射な脚の通常の pushout のホモトピー引き戻しの貼り合わせ

概要：両 span の右脚が単射なら、homotopy-cartesian な二面から通常の余極限の各頂点を得る。
方針：Lemma 1.7 と、二重写像円筒から具体的な余極限への局所化同型を四頂点で比較する。
規約：Segal 1974 Proposition 1.6 の有限骨格の実際の付着への移送。
使われ方：fat realization の境界に沿う有限骨格の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits
open SerrePositivity.SimplicialModel

/--
概要：単射な右脚の span の homotopy-cartesian な比較は、通常の余極限への各頂点もそうする。
方針：実際の円筒の貼り合わせと余極限への比較の可逆性を使う。
規約：両余錐の普遍性と比較の可換性だけを構造的な入力とし、結論を仮定しない。
使われ方：各有限骨格の境界に沿う pushout の比較。
-/
@[kerodon 011T]
theorem spanPushout_vertex_homotopyPullback {F G : WalkingSpan ⥤ SSet.{u}}
    [Mono (F.map WalkingSpan.Hom.snd)] [Mono (G.map WalkingSpan.Hom.snd)]
    (α : F ⟶ G)
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α))
    (c : Cocone F) (hc : IsColimit c) (c' : Cocone G) (hc' : IsColimit c')
    (p : c.pt ⟶ c'.pt) (hp : ∀ d, c.ι.app d ≫ p = α.app d ≫ c'.ι.app d) (d : WalkingSpan) :
    IsHomotopyPullback (show CommSq (c.ι.app d) (α.app d) p (c'.ι.app d) from ⟨hp d⟩) := by
  have h := spanCylinder_vertex_homotopyPullback α hL hR d
  apply (isHomotopyPullback_iff_of_localized_isIso
    (naturalitySquare (spanCylinderVertex d) α) (⟨hp d⟩ : CommSq _ _ _ _)
    (𝟙 _) (spanCylinderToColimit F c hc) (𝟙 _) (spanCylinderToColimit G c' hc')
    ?_ (by simp) ?_ ?_ (by infer_instance)
    (spanCylinderToColimit_localized_isIso F c hc) (by infer_instance)
    (spanCylinderToColimit_localized_isIso G c' hc')).mp h
  · rw [spanCylinderVertex_toColimit, Category.id_comp]
  · exact spanCylinderToColimit_naturality α c hc c' hc' p hp
  · rw [spanCylinderVertex_toColimit, Category.id_comp]

end SerrePositivity.KST.Comparison
