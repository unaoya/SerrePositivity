module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalityInversion
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoYonedaConeLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTransportComponents

/-!
概要：同じ局所性を全共変 Hom 関手の自然比較成分の可逆性で判定する。
方針：共同 Hom の反変変数の辺作用を評価し、元の表現可能前層の辺作用と同定する。
規約：同じ指定辺から一つの全自然比較を作る。
使われ方：局所性の filtered 余極限閉性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：指定辺による元の全共変 Hom 関手間の反変な自然比較。
方針：元の co-Yoneda で反対辺を写し、両端を元の共変 Hom へ正規化する。
規約：全関手圏の二胞体を使用する。
使われ方：全パラメータでの局所性比較。 -/
def localPrecompositionComparison {C : SSet.{u}} [Quasicategory C] {x y : C _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj C) x y) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant x) :=
  eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex y)).symm ≫
    Truncated.HomotopyCategory.homMk
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C)))) ≫
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex x))

private lemma normalizedEdgeEvaluation_isIso_iff {K X : SSet.{u}}
    {U V : K ⟶ X} {a b : ((ihom K).obj X) _⦋0⦌}
    (d : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) a b)
    (ha : a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (hb : b = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) (k : K _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (eqToHom (congrArg HomotopyCategory.mk ha).symm ≫
        Truncated.HomotopyCategory.homMk d ≫
        eqToHom (congrArg HomotopyCategory.mk hb)) k) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (d.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomEvaluate_isIso_iff]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
  rw [isIso_comp_left_iff (eqToHom _) (_ ≫ _),
    isIso_comp_right_iff _ (eqToHom _)]
  rfl

private lemma mappedEdge_evaluation_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {x y : X _⦋0⦌} (d : Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((d.map ((truncation 2).map f)).map ((truncation 2).map g)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (d.map ((truncation 2).map (f ≫ g))) := by
  rfl

/-- 概要：同じ自然比較の元の対象での可逆性は指定辺の局所性と同値。
方針：評価による端点の同型を消去し、共同 Hom の評価を元の表現可能前層へ戻す。
規約：同じ比較成分と元の局所性を使用する。
使われ方：指定余極限の比較成分の可逆性判定。 -/
lemma localPrecompositionComparison_isIso_iff {C : SSet.{u}} [Quasicategory C]
    {x y : C _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (z : C _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (localPrecompositionComparison e) (ULift.up z)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (Truncated.HomotopyCategory.homMk e) z := by
  have h := normalizedEdgeEvaluation_isIso_iff
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex x) (ULift.up z)
  have hcomp := mappedEdge_evaluation_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coyonedaInfinityMap_evaluation] at hcomp
  exact h.trans (hcomp.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_representableInverts z e).symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
