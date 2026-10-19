module
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberSuspensionHom
public import SerrePositivity.InfinityCategories.Derived.CofiberSuspensionSquareComponents

/-! # 包含像へ正規化した cofiber 比較射の成分

概要：正規化した周囲の比較は始点で恒等射、終点で標準 cone 写像の類を持つ。
方針：両端の選択された等式輸送を Arrow 表示で打ち消す。
規約：包含前の表示との違いは型付きの恒等成分に含める。使われ方：D7 の Semifree への反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 包含後の比較の始点成分は、その始点の恒等射。 -/
lemma cofiberSuspensionHomOnInclusion_source_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk (𝟙 ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).obj
        (SSet.HomotopyCategory.mk (functorVertex
          ((semifreeCofiberZeroTriangle f).square ≫ derivedInfinityInclusion))))) := by
  have h : Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
      (cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
        (cofiberToSuspensionSquareHom f)) := by
    unfold cofiberSuspensionHomOnInclusion
    rw [CategoryTheory.Functor.map_comp, arrowMk_map_chosenEqToHom_comp,
      CategoryTheory.Functor.map_comp, arrowMk_map_comp_chosenEqToHom]
  exact arrowMk_eq_id_source _ (h.trans (cofiberToSuspensionSquareHom_source_arrow f))

/-- 包含後の比較の終点成分は標準 cone 写像の類。 -/
lemma cofiberSuspensionHomOnInclusion_target_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
      (cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (cofiberToSuspensionMap f)).toTruncated) := by
  unfold cofiberSuspensionHomOnInclusion
  rw [CategoryTheory.Functor.map_comp, arrowMk_map_chosenEqToHom_comp,
    CategoryTheory.Functor.map_comp, arrowMk_map_comp_chosenEqToHom]
  exact cofiberToSuspensionSquareHom_target_arrow f

end SerrePositivity.InfinityCategories
