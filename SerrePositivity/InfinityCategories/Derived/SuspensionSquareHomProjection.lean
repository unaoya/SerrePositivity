module
public import SerrePositivity.InfinityCategories.Derived.SuspensionSquareHomotopy
public import SerrePositivity.InfinityCategories.Derived.SuspensionSquareAmbientComponents

/-! # 持ち上げた suspension 四角形の射の包含像

概要：Semifree 内へ持ち上げた比較射は、包含後に構成済みの周囲の射に一致する。
方針：ホモトピーの包含の等式を curry し、選んだ辺の類の式で射を同定する。
規約：端点の表示の差は Arrow に含める。使われ方：D7 の端点成分を Semifree へ反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 持ち上げた比較射の包含像は元の周囲の比較射。 -/
lemma semifreeSuspensionSquareHom_inclusion_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((hoFunctor.map
      ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map derivedInfinityInclusion)).toFunctor.map
        (semifreeSuspensionSquareHom a)) =
      Arrow.mk (suspensionComplexSquareHomOnInclusion a) := by
  calc
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (suspensionComplexSquareEdge a)) := by
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      change ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map derivedInfinityInclusion).app _
        (SSet.yonedaEquiv (curry (semifreeSuspensionSquareHomotopy a).h)) = _
      rw [← SSet.yonedaEquiv_comp, ← curry_natural_right,
        semifreeSuspensionSquareHomotopy_inclusion]
      change SSet.yonedaEquiv
        (curry (uncurry (SSet.yonedaEquiv.symm (suspensionComplexSquareEdge a).edge))) = _
      rw [curry_uncurry, Equiv.apply_symm_apply]
    _ = _ := congrArg Arrow.mk (suspensionComplexSquareEdge_homMk a)

/-- 周囲の端点表示の輸送を含む比較の始点成分は元の鎖写像。 -/
lemma suspensionComplexSquareHomOnInclusion_source_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (suspensionComplexSquareHomOnInclusion a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (complexEdge a).toTruncated) := by
  unfold suspensionComplexSquareHomOnInclusion
  rw [Functor.map_comp, arrowMk_map_chosenEqToHom_comp, Functor.map_comp,
    arrowMk_map_comp_chosenEqToHom]
  exact suspensionComplexSquareHom_source_arrow a

/-- 周囲の端点表示の輸送を含む比較の終点成分は標準 cone 写像。 -/
lemma suspensionComplexSquareHomOnInclusion_target_arrow (a : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (suspensionComplexSquareHomOnInclusion a)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (semifreeSuspensionComplexMap a)).toTruncated) := by
  unfold suspensionComplexSquareHomOnInclusion
  rw [Functor.map_comp, arrowMk_map_chosenEqToHom_comp, Functor.map_comp,
    arrowMk_map_comp_chosenEqToHom]
  exact suspensionComplexSquareHom_target_arrow a

end SerrePositivity.InfinityCategories
