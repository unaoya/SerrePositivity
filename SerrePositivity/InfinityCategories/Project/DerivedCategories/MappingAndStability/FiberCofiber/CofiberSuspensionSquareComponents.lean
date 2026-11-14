module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberSuspensionSquareHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquareMiddleComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexSquareHomEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowIdentityComposition

/-! # Cofiber から suspension の四角形比較の両端成分

概要：二段比較の始点は恒等射、終点は標準 cone 写像になる。
方針：中間対象の変更の恒等成分を消し、後合成比較の成分を使う。
規約：端点表示の等式も Arrow に含める。使われ方：D7 の接続射の一意性への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S] {A B : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 正規化した中間対象比較の両端成分は恒等射。 -/
lemma cofiberToSuspensionMiddleHomotopy_corner_arrow (f : A ⟶ B) (i : Fin 2) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) i i).map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMiddleHomotopy f)))) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).square
          i i)) := by
  have h := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).changeBottomMiddleHomotopy_corner_arrow (0 : B ⟶ 0)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionRightFactor f) i
  refine Eq.trans ?_ h
  exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) i i).mapArrow.obj
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyOfEndpoints_functorHom_arrow
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcompose
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).changeBottomMiddleHomotopy (0 : B ⟶ 0)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB (0 : A ⟶ 0) (0 : A ⟶ 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionRightFactor f)) rfl
      (congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A 0 0
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber (0 : A ⟶ 0) (0 : A ⟶ 0)) => k.square)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionIntermediateData_eq f)))

/-- 標準 cofiber から suspension の比較の始点成分は恒等射。 -/
lemma cofiberToSuspensionSquareHom_source_arrow (f : A ⟶ B) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom f)) =
      Arrow.mk (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).square 0 0)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom
  rw [CategoryTheory.Functor.map_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_comp_of_right_identity _ _
    (cofiberToSuspensionMiddleHomotopy_corner_arrow f 0)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_id_source _
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeHom_source_arrow
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)))

/-- 標準 cofiber から suspension の比較の終点成分は指定した cone 写像。 -/
lemma cofiberToSuspensionSquareHom_target_arrow (f : A ⟶ B) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).toTruncated) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionSquareHom
  rw [CategoryTheory.Functor.map_comp]
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_comp_of_right_identity _ _
    (cofiberToSuspensionMiddleHomotopy_corner_arrow f 1)).trans
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberComplexSquareData f (0 : A ⟶ 0)).postcomposeHom_target_arrow
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
