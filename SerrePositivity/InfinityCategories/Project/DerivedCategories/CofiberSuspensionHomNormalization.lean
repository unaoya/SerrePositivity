module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeCofiberSuspensionHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberSuspensionSquareComponents

/-! # 包含像へ正規化した cofiber 比較射の成分

概要：正規化した周囲の比較は始点で恒等射、終点で標準 cone 写像の類を持つ。
方針：両端の選択された等式輸送を Arrow 表示で打ち消す。
規約：包含前の表示との違いは型付きの恒等成分に含める。使われ方：D7 の Semifree への反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- 包含後の比較の始点成分は、その始点の恒等射。 -/
lemma cofiberSuspensionHomOnInclusion_source_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion))))) := by
  have h : Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom f)) := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion
    rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_chosenEqToHom_comp,
      CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_comp_chosenEqToHom]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_id_source _ (h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom_source_arrow f))

/-- 包含後の比較の終点成分は標準 cone 写像の類。 -/
lemma cofiberSuspensionHomOnInclusion_target_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).toTruncated) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion
  rw [CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_chosenEqToHom_comp,
    CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_map_comp_chosenEqToHom]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom_target_arrow f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
