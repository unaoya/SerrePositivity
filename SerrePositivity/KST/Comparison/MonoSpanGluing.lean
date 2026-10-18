module

public import SerrePositivity.KST.Comparison.SpanStrictification
public import SerrePositivity.KST.Comparison.SpanCylinderInvariance
public import SerrePositivity.KST.Comparison.StrictCylinderHomotopyPullbacks

/-!
# 単射な基底の span のホモトピー引き戻しの貼り合わせ

概要：単射な二つの基底射と Kan な中央の基底の下で、homotopy-cartesian な span を円筒へ貼り合わせる。
方針：共通の trivial fibration の延長による厳密化と、円筒の四角形の不変性を使う。
規約：Segal 1974 Lemma 1.7 のこの条件の下での証明。一般の基底への還元は別に扱う。
使われ方：基底の二射を単射に置き換えた後の貼り合わせ。
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
概要：単射な二つの基底射の下で、homotopy-cartesian な span の円筒への三頂点の四角形はホモトピー引き戻し。
方針：厳密な模型への二本の成分ごとの局所化同型で、厳密な場合の結論を戻す。
規約：中央の基底は Kan、三つの縦射は Kan fibration とする。
使われ方：Segal Lemma 1.7 の一般の場合への還元先。
-/
theorem spanCylinder_vertex_homotopyPullback_of_mono {F G : WalkingSpan ⥤ SSet.{u}}
    [SSet.KanComplex (G.obj .zero)] [Mono (G.map WalkingSpan.Hom.fst)]
    [Mono (G.map WalkingSpan.Hom.snd)] (α : F ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α))
    (d : WalkingSpan) : IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) := by
  obtain ⟨H, K, u, v, β, hfac, hu, hv, hβ, hβL, hβR⟩ :=
    spanStrictification_of_mono α hα hL hR
  have hstrict := doubleMappingCylinder_homotopyPullbacks_of_strict hβL hβR
    (hβ .zero) (hβ .left) (hβ .right)
  have hβd : IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) β) := by
    rcases d with (_ | _ | _)
    · exact hstrict.2.2
    · exact hstrict.1
    · exact hstrict.2.1
  have hId (e : WalkingSpan) : IsIso (AnodyneHomotopy.anodyneQ.map (𝟙 (G.obj e))) := by
    infer_instance
  have hU := spanCylinder_vertexSquare_map_iff (u ≫ α) α u (𝟙 G) (by simp) hu hId d
  have hV := spanCylinder_vertexSquare_map_iff (v ≫ β) β v (𝟙 G) (by simp) hv hId d
  exact hU.mp (hfac.symm ▸ hV.mpr hβd)

end SerrePositivity.KST.Comparison
