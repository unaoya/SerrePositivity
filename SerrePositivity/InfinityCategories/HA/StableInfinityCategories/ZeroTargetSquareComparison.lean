module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareColumnComparison

/-! # 最後の成分が零になる suspension への比較

概要：四角形から右下の頂点の suspension へ、始点成分が下辺、最後の成分が零となる比較がある。
方針：右の列へ変形し、終対象への列を比較し、左の列から suspension へ変形する。
規約：元の四角形の普遍性は不要。
使われ方：S4 の接続射の後の Σf との零合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：右下の頂点の suspension への比較で下辺を始点成分に、零射を最後の成分にできる。
方針：三つの水平・列の比較を合成し、中間の最後の成分が零対象に入ることを使う。
規約：始点の表示の輸送を eqToHom で含める。使われ方：接続射の後の零合成。 -/
lemma exists_squareToSuspension_zero_target {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0)) :
    ∃ q : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s.square),
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map q = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom F ≫
        eqToHom (congrArg SSet.HomotopyCategory.mk s.source_eq.symm) ∧
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map q = 0 := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_squareRightToSuspensionLeft F s
  let a := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalRightHomotopy F))
  let b := SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (snd (Δ[1] : SSet.{u}) Δ[1]) H))
  let c := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy s.square))
  let e : @Quiver.Hom (hoFunctor.obj X) _ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex F 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0) :=
    eqToHom (show _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex F 1 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0 from
      congrArg SSet.HomotopyCategory.mk s.source_eq.symm)
  have ha : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map a = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom F :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalRightHomotopy_source F
  have hb : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map b = e := by
    obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnHomotopy_source_arrow H (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 0) hH)
    simpa only [b, e, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation, eqToHom_refl, Category.id_comp] using hf
  have hc : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map c = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareHorizontalLeftHomotopy_source s.square
  have hbzero : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map b = 0 :=
    s.zero_corner.isZeroHo.eq_zero_of_tgt (C := hoFunctor.obj X) _
  refine ⟨a ≫ b ≫ c, ?_, ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, ha, hb, hc]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom F ≫ (e ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex s.square 0 0)) = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom F ≫ e
    rw [Category.comp_id]
  · rw [Functor.map_comp, Functor.map_comp, hbzero, zero_comp (C := hoFunctor.obj X),
      comp_zero (C := hoFunctor.obj X)]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
