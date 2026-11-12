module

public import SerrePositivity.KST.Comparison.KanBaseSpanGluing
public import SerrePositivity.KST.Comparison.DiagramExInfinity

/-!
# 二重写像円筒のホモトピー引き戻しの貼り合わせ

概要：homotopy-cartesian な span の射は、二重写像円筒への各頂点の四角形も homotopy-cartesian にする。
方針：縦射を Kan 分解し、Ex∞ で基底を Kan にし、単射な基底の厳密化から結論を戻す。
規約：Segal 1974 Lemma 1.7。原典の WCHP の経路とは異なる部分切断による延長を使う。
使われ方：Segal Proposition 1.6 の骨格の貼り合わせと telescope の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Functor

/--
概要：三つの縦射が Kan fibration の homotopy-cartesian な span は、円筒への各頂点のホモトピー引き戻しを与える。
方針：Ex∞ で基底を Kan に置換し、円筒の模型の不変性で結論を元へ戻す。
規約：水平射と基底には条件を課さない。
使われ方：縦射の関手的な Kan 分解の後の Segal Lemma 1.7。
-/
theorem spanCylinder_vertex_homotopyPullback_of_fibrations {F G : WalkingSpan ⥤ SSet.{u}}
    (α : F ⟶ G) (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α))
    (d : WalkingSpan) : IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) := by
  let : SSet.KanComplex ((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity).obj .zero) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex (G.obj .zero)
  let αR := whiskerRight α _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
  have hαR (e : WalkingSpan) : SSet.modelCategoryQuillen.J.rlp (αR.app e) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_rlp (α.app e) (hα e)
  have hLR := (diagramExInfinity_arrowSquare_iff α WalkingSpan.Hom.fst).mpr hL
  have hRR := (diagramExInfinity_arrowSquare_iff α WalkingSpan.Hom.snd).mpr hR
  have hR := spanCylinder_vertex_homotopyPullback_of_kan_base αR hαR hLR hRR d
  exact (spanCylinder_vertexSquare_map_iff α αR (diagramExInfinityUnit F) (diagramExInfinityUnit G)
    (diagramExInfinityUnit_naturality α) (diagramExInfinityUnit_localized_isIso F)
    (diagramExInfinityUnit_localized_isIso G) d).mpr hR

/--
概要：homotopy-cartesian な span の射から、二重写像円筒への三頂点のホモトピー引き戻しを得る。
方針：図式の射の関手的な anodyne–Kan 分解で縦射を Kan fibration とし、置換の不変性を使う。
規約：Segal 1974 Lemma 1.7。Kan 性や厳密な引き戻し性を追加仮定にはしない。
使われ方：Segal の比較定理の骨格ごとの貼り合わせ。
-/
theorem spanCylinder_vertex_homotopyPullback {F G : WalkingSpan ⥤ SSet.{u}}
    (α : F ⟶ G)
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α))
    (d : WalkingSpan) : IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) := by
  have hβ := diagramKanProjection_rlp α
  have hβL := (diagramKan_arrowSquare_iff α WalkingSpan.Hom.fst).mp hL
  have hβR := (diagramKan_arrowSquare_iff α WalkingSpan.Hom.snd).mp hR
  have h := spanCylinder_vertex_homotopyPullback_of_fibrations
    (diagramKanProjection α) hβ hβL hβR d
  exact (spanCylinderKan_vertexSquare_iff α d).mpr h

end SerrePositivity.KST.Comparison
