module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.SuspensionSquareHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.SuspensionSquareAmbientComponents

/-! # 持ち上げた suspension 四角形の射の包含像

概要：Semifree 内へ持ち上げた比較射は、包含後に構成済みの周囲の射に一致する。
方針：ホモトピーの包含の等式を curry し、選んだ辺の類の式で射を同定する。
規約：端点の表示の差は Arrow に含める。使われ方：D7 の端点成分を Semifree へ反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 持ち上げた比較射の包含像は元の周囲の比較射。 -/
lemma semifreeSuspensionSquareHom_inclusion_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((hoFunctor.map
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHom a)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion a) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareEdge a)) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      change ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).app _
        (SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHomotopy a).h)) = _
      rw [← SSet.yonedaEquiv_comp, ← curry_natural_right,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquareHomotopy_inclusion]
      change SSet.yonedaEquiv
        (curry (uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareEdge a).edge))) = _
      rw [curry_uncurry, Equiv.apply_symm_apply]
    _ = _ := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareEdge_homMk a)

/-- 周囲の端点表示の輸送を含む比較の始点成分は元の鎖写像。 -/
lemma suspensionComplexSquareHomOnInclusion_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge a).toTruncated) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_chosenEqToHom_comp, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_comp_chosenEqToHom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHom_source_arrow a

/-- 周囲の端点表示の輸送を含む比較の終点成分は標準 cone 写像。 -/
lemma suspensionComplexSquareHomOnInclusion_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexMap a)).toTruncated) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHomOnInclusion
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_chosenEqToHom_comp, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_comp_chosenEqToHom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.suspensionComplexSquareHom_target_arrow a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
