module
public import SerrePositivity.KST.SConstruction.SplitFibrationPullback
public import SerrePositivity.KST.SConstruction.RealizationConnected
public import SerrePositivity.KST.Comparison.DiagramExInfinity

/-! # 連結基底の図式で切断から退縮へ移す面条件
概要：図式の自然変換において、連結な基底を持つ退縮の面条件を、その切断から検出する。
方針：関手的な Kan 分解で二つの縦射を置換し、必要なら Ex∞ で基底を Kan にする。
規約：元の行に Kan 性を課さず、実際の自然性四角形を扱う。使われ方：経路境界の δ₀。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open scoped Simplicial

/-- Kan な連結基底を持つ図式の退縮四角形は切断四角形から検出できる。 -/
lemma naturality_homotopyPullback_retraction_of_section_of_kan
    {D : Type v} [Category.{w} D] {F G : D ⥤ SSet.{u}} (α : F ⟶ G)
    {d e : D} (s : d ⟶ e) (r : e ⟶ d) (hsr : s ≫ r = 𝟙 d)
    [KanComplex (G.obj e)] [SSet.IsPreconnected (G.obj e)] (b : (G.obj d) _⦋0⦌)
    (hsec : IsHomotopyPullback (CommSq.mk (α.naturality s))) :
    IsHomotopyPullback (CommSq.mk (α.naturality r)) := by
  apply (diagramKan_arrowSquare_iff α r).mpr
  let γ := diagramKanProjection α
  have hs : IsHomotopyPullback (CommSq.mk (γ.naturality s)) :=
    (diagramKan_arrowSquare_iff α s).mp hsec
  apply homotopyPullback_retraction_of_section (γ.app d) (diagramKanProjection_rlp α d)
    (γ.app e) (diagramKanProjection_rlp α e)
    ((diagramKanMiddle α).map s) (G.map s) ((diagramKanMiddle α).map r) (G.map r)
    (γ.naturality s) (γ.naturality r) ?_ ?_ b hs
  · rw [← CategoryTheory.Functor.map_comp, hsr, CategoryTheory.Functor.map_id]
  · rw [← G.map_comp, hsr, G.map_id]

/-- 元の行の Kan 性を要求せず、連結な基底を持つ退縮四角形を切断四角形から検出する。 -/
lemma naturality_homotopyPullback_retraction_of_section
    {D : Type v} [Category.{w} D] {F G : D ⥤ SSet.{u}} (α : F ⟶ G)
    {d e : D} (s : d ⟶ e) (r : e ⟶ d) (hsr : s ≫ r = 𝟙 d)
    [SSet.IsConnected (G.obj e)] (b : (G.obj d) _⦋0⦌)
    (hsec : IsHomotopyPullback (CommSq.mk (α.naturality s))) :
    IsHomotopyPullback (CommSq.mk (α.naturality r)) := by
  let R := Functor.whiskerRight α _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity
  let : SSet.IsConnected ((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity).obj e) :=
    isConnected_of_anodyne (A := G.obj e) (B := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (G.obj e))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (G.obj e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _)
  let : KanComplex ((G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity).obj e) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex (G.obj e)
  have hs : IsHomotopyPullback (CommSq.mk (R.naturality s)) :=
    (isHomotopyPullback_exInfinity_iff (CommSq.mk (α.naturality s))).mpr hsec
  apply (isHomotopyPullback_exInfinity_iff (CommSq.mk (α.naturality r))).mp
  exact naturality_homotopyPullback_retraction_of_section_of_kan R s r hsr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (G.obj d)).app _ b) hs

end SerrePositivity.KST.SConstruction
