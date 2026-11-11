module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGObjectImageNerve
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # dg Yoneda の表現可能部分との実際の ∞ 圏同値

概要：代表加群間の全 Hom 複体で作るラベル付き dg 圏と元の nerve を比較する。
方針：dg Yoneda の Hom 複体同型を充満像の一般定理へ渡す。
規約：元の対象型をラベルとし、全加群圏より小さい宇宙で扱う。
使われ方：β3 の前三角 dg 圏の nerve の安定性の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 対象ラベル D と代表加群間の全 Hom 複体を持つ dg 圏。 -/
abbrev RepresentableDGCategory := _root_.SerrePositivity.InfinityCategories.DGObjectImage (dgYoneda A D).obj

/-- 元の dg 圏から表現可能部分への dg Yoneda 関手。 -/
abbrev representableDGYoneda : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D (RepresentableDGCategory A D) :=
  _root_.SerrePositivity.InfinityCategories.dgFunctorToObjectImage (dgYoneda A D)

/-- ラベル付き表現可能部分の全 Hom 複体は dg Yoneda によって元の Hom と同型。 -/
lemma representableDGYoneda_hom_isIso (x y : D) :
    IsIso ((representableDGYoneda A D).map x y) := by
  change IsIso (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y)
  unfold _root_.SerrePositivity.DifferentialGraded.yonedaHom
  infer_instance

/-- 表現可能部分の nerve への Yoneda 関手は実際の写像空間で充満忠実。 -/
lemma representableDGYonedaNerve_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (representableDGYoneda A D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso _ (representableDGYoneda_hom_isIso A D)

/-- 元の dg nerve と全 Hom 複体を持つ表現可能部分の nerve の明示的同値。 -/
def dgYonedaRepresentableNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RepresentableDGCategory A D)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgObjectImageNerveEquivalenceOfHomIso (dgYoneda A D)
    (representableDGYoneda_hom_isIso A D)

/-- 表現可能部分との同値の順方向は実際の dg Yoneda 関手の nerve。 -/
lemma dgYonedaRepresentableNerveEquivalence_hom :
    (dgYonedaRepresentableNerveEquivalence A D).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (representableDGYoneda A D) := rfl

/-- 表現可能部分の評価との合成は全 dg 加群圏への元の Yoneda 関手に厳密に等しい。 -/
lemma representableDGYoneda_evaluation :
    (representableDGYoneda A D).comp (_root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation A (dgYoneda A D).obj) =
      dgYoneda A D := _root_.SerrePositivity.InfinityCategories.dgFunctorToObjectImage_evaluation _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
