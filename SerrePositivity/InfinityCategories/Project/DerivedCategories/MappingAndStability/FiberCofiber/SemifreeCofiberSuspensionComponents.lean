module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberSuspensionHomNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ChainMapEdge
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ArrowFaithfulReflection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquareEvaluationPostcomposition

/-! # Semifree 内の cofiber 比較の両端成分

概要：Semifree に持ち上げた比較は、始点で恒等射、終点で cone 写像の類を持つ。
方針：包含後の評価を反映し、全複体の成分計算と鎖写像の辺の式を使う。
規約：任意の semifree 間の鎖写像。使われ方：D7 の接続射の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S}

/-- Semifree の cofiber 比較の始点成分は恒等射。 -/
lemma semifreeCofiberSuspensionHom_source_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) 0 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f)) =
      Arrow.mk (𝟙 ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) 0 0).obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f).square)))) := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_of_faithful_map (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_obj_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))
  calc
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f))) :=
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_postcomp_arrow _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f) 0 0).symm
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion f)) :=
      congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 0 0).mapArrow.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom_inclusion_arrow f)
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion_source_arrow, CategoryTheory.Functor.map_id]
      rfl

/-- Semifree の cofiber 比較の終点成分は cone 写像の類。 -/
lemma semifreeCofiberSuspensionHom_target_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) 1 1).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
          (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f))) := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_faithful S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S)
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.arrowMk_eq_of_faithful_map (hoFunctor.map _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullInclusionHo_obj_injective S (Complex S) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S))
  calc
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f))) :=
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation_postcomp_arrow _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityInclusion
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom f) 1 1).symm
    _ = Arrow.mk ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion f)) :=
      congrArg (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) 1 1).mapArrow.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSuspensionHom_inclusion_arrow f)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)).toTruncated) :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSuspensionHomOnInclusion_target_arrow f
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_inclusion (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroObject f))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberToSuspensionMap f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
