module

public import SerrePositivity.KST.Comparison.MonoSpanGluing
public import SerrePositivity.KST.Comparison.SpanMonoBase
public import SerrePositivity.KST.Comparison.DiagramBaseChange

/-!
# Kan な中央の基底での span の貼り合わせ

概要：中央の基底が Kan なら、水平射の単射性なしで homotopy-cartesian な span を円筒へ貼り合わせる。
方針：基底の二射を mono 分解し、縦の Kan fibration を引き戻して単射な基底の場合へ移す。
規約：Segal 1974 Lemma 1.7 の Kan な中央の基底の場合。
使われ方：Ex∞ で中央の基底を Kan に置換した後の貼り合わせ。
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
概要：Kan な中央の基底の下で、homotopy-cartesian な span の円筒への各頂点の四角形はホモトピー引き戻し。
方針：単射な基底への置換と right properness で、元の図式の仮定と円筒の結論を移す。
規約：三つの縦射を Kan fibration とし、水平射には条件を課さない。
使われ方：Segal Lemma 1.7 の一般の場合への還元先。
-/
theorem spanCylinder_vertex_homotopyPullback_of_kan_base {F G : WalkingSpan ⥤ SSet.{u}}
    [SSet.KanComplex (G.obj .zero)] (α : F ⟶ G)
    (hα : ∀ d, SSet.modelCategoryQuillen.J.rlp (α.app d))
    (hL : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) α))
    (hR : IsHomotopyPullback (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) α))
    (d : WalkingSpan) : IsHomotopyPullback (naturalitySquare (spanCylinderVertex d) α) := by
  let ν := spanMonoBaseProjection G
  let α₀ := pullback.fst ν α
  have hν := spanMonoBaseProjection_localized_isIso G
  have hα₀ := diagramPullback_fst_rlp α ν hα
  have hL₀ := (diagramPullback_arrowSquare_iff α ν hα hν WalkingSpan.Hom.fst).mpr hL
  have hR₀ := (diagramPullback_arrowSquare_iff α ν hα hν WalkingSpan.Hom.snd).mpr hR
  have h₀ := spanCylinder_vertex_homotopyPullback_of_mono α₀ hα₀ hL₀ hR₀ d
  exact (spanCylinder_vertexSquare_map_iff α₀ α (pullback.snd ν α) ν
    (pullback.condition (f := ν) (g := α))
    (diagramPullback_snd_localized_isIso α ν hα hν) hν d).mp h₀

end SerrePositivity.KST.Comparison
