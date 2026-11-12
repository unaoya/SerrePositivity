module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：h Fun の任意の二胞体を実際のホモトピーで表す。
方針：quasicategory の Hom の辺代表を選び、内部 Hom の辺を uncurry する。
規約：可逆な二胞体には制限しない。
使われ方：指定単位を矢印の族として comma の切断へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

/-- 概要：h Fun の射の実際のホモトピー代表。
方針：辺の全射性で代表を選び、curry の逆で戻す。
規約：標的 X は quasicategory、始域 A は任意。
使われ方：単位や余単位を具体的な図式として扱う。 -/
noncomputable def functorHomHomotopy {A X : SSet.{u}} [Quasicategory X] {U V : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) : SSet.Homotopy U V :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
    (Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) α))

/-- 概要：選んだホモトピー代表の辺の類は元の二胞体。
方針：辺とホモトピーの往復を計算し、代表の選択の仕様を使う。
規約：元の射 α との等式を記録する。
使われ方：代表の選択で単位の類を変更しないことの検証。 -/
lemma functorHomHomotopy_hom {A X : SSet.{u}} [Quasicategory X] {U V : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (functorHomHomotopy α)) = α := by
  let e := Classical.choose
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) α)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (functorHomHomotopy α) = e := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm e.edge))) = e.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  rw [he]
  exact Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V) α)

/-- 概要：ホモトピーを関手の辺にして戻すと元のホモトピー。
方針：Yoneda 表示と curry・uncurry の両逆を使う。
規約：非可逆なホモトピーでも成立する。
使われ方：各点の成分を選んだ代表から計算する。 -/
lemma simplicialHomotopyOfFunctorEdge_of_homotopy {A X : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) = H := by
  apply SSet.RelativeMorphism.Homotopy.ext
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
  rw [Equiv.symm_apply_apply, uncurry_curry]

/-- 概要：ホモトピーの辺の類の評価はそのホモトピーの頂点成分の辺の類。
方針：評価で写した代表辺と頂点を通る辺を比較し、両端を輸送する。
規約：始域・標的の quasicategory 性は不要。
使われ方：単位の代表と各点の標準比較の成分を結ぶ。 -/
lemma functorHomEvaluate_homotopy {A X : SSet.{u}} {U V : A ⟶ X}
    (H : SSet.Homotopy U V) (x : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex x V)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) x
  rw [simplicialHomotopyOfFunctorEdge_of_homotopy] at h
  exact h.symm

/-- 概要：選んだ二胞体のホモトピー代表は各点でも元の評価を表す。
方針：辺の類の回収と頂点評価の公式を合わせる。
規約：標的 X は quasicategory。
使われ方：comma の切断の矢印の成分が指定単位であることの認識。 -/
lemma functorHomHomotopy_component {A X : SSet.{u}} [Quasicategory X] {U V : A ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (x : A _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (functorHomHomotopy α) x).toTruncated =
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x := by
  have h := functorHomEvaluate_homotopy (functorHomHomotopy α) x
  rw [functorHomHomotopy_hom] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
