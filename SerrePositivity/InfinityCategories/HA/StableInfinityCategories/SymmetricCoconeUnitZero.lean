module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialFiberZeroFactor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeFoldUnit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EdgeTerminalCocone

/-! # 対称 span のループ単位と Hom の零射

概要：零対象へ向かう同じ二枝の span では、対角から得るループ単位の Hom 表示は零射。
方針：単位を畳んだ辺の余錐で表し、辺の終点余錐の零頂点を通る因子分解を使う。
規約：X の安定性全体は不要で、余極限余錐と零射構造を仮定する。使われ方：演算を加法に同定する単位条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：辺の終点余錐の頂点は元の辺の終点である。
方針：終点への制限が定値の恒等余錐である式を頂点で読む。
規約：値域の充填性は不要。使われ方：畳んだ余錐の零頂点の指定。 -/
lemma edgeTerminalCocone_vertex {X : SSet.{u}} (g : (Δ[1] : SSet.{u}) ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).vertex = SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ g) := by
  rw [← (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone g).vertex_restrict (stdSimplex.δ (0 : Fin 2)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_restrict_val, SSet.comp_const,
    ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]

/-- 概要：零対象を終点とする辺の余錐を畳み込みで送ると、全 span の Hom 表示では零射になる。
方針：辺の終点余錐の始対象性と零頂点を、同じ底上の関手による零因子分解へ与える。
規約：全 span の指定余錐は余極限、X は quasicategory で h X に零射がある。
使われ方：対角の成分から得る単位を零射に同定する。 -/
lemma coconeMappingSpacePiZeroEquiv_fold_eq_zero {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms X.HomotopyCategory] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeFold f y) a) = 0 := by
  let F : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm f.edge
  let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone F
  have hv : d.vertex = z := by
    have ht := congrArg (SSet.yonedaEquiv (X := X) (n := ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target f)
    exact (edgeTerminalCocone_vertex F).trans (ht.trans (SSet.yonedaEquiv.apply_symm_apply z))
  have hd : IsZero (SSet.HomotopyCategory.mk d.vertex : hoFunctor.obj X) :=
    hz.isZeroHo.of_iso (eqToIso
      (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj X)) hv))
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_map_eq_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricSpanFoldCoslice f) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricSpanFoldCoslice_projection f)
    c hc d (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeTerminalCocone_isColimit F) hd y a

/-- 概要：対称 span の対角から得るループ単位は、余極限頂点からの Hom 表示で零射となる。
方針：単位を畳み込んだ枝の基点として表し、畳んだ余錐の零射の公式を使う。
規約：零頂点と余極限余錐、h X の零射構造だけを使う。使われ方：加法の一般判定の単位条件。 -/
lemma symmetricCoconeLoopUnit_hom_eq_zero {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms X.HomotopyCategory] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpacePiZeroEquiv c hc y (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit f y e) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeLoopUnit_eq_fold]
  exact coconeMappingSpacePiZeroEquiv_fold_eq_zero f hz c hc y (SSet.π₀.mk e)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
