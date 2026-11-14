module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：既存の指定関手同型の成分は、同じ同型を元の一点評価で写したものである。
方針：ホモトピー圏の評価を生成辺で比較し端点の表示変更だけを除く。
規約：指定同型の値を保持。使われ方：元の三角形比較の一点での成分の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries

/-- 端点の対象の表示変更だけでは元の指定同型の値は変わらない。 -/
lemma iso_endpoints_heq {C : Type u} [Category C] {a b a' b' : C}
    (e : a ≅ b) (ha : a = a') (hb : b = b') :
    HEq ((eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb) e := by
  subst a'
  subst b'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  rfl

/-- 対象の表示変更を保つ同型の一致は任意の関手で写しても保たれる。 -/
lemma mapIso_heq_of_heq {C D : Type u} [Category C] [Category D] (F : C ⥤ D)
    {a b a' b' : C} (e : a ≅ b) (e' : a' ≅ b') (ha : a = a') (hb : b = b')
    (he : HEq e e') : HEq (F.mapIso e) (F.mapIso e') := by
  subst a'
  subst b'
  cases eq_of_heq he
  rfl

/-- ホモトピー圏の関手への評価と元の一点評価は同じ通常の関手を与える。 -/
lemma functorHomotopyEvaluation_evaluate {X Y : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation X Y ⋙
        (evaluation (hoFunctor.obj X) (hoFunctor.obj Y)).obj (SSet.HomotopyCategory.mk x) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) x)).toFunctor := by
  refine SSet.Truncated.HomotopyCategory.functor_ext ?_ ?_
  · intro F
    change SSet.HomotopyCategory.mk (F.app _ (𝟙 _) x) =
      SSet.HomotopyCategory.mk (F.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  · intro a b e
    have ha : a.app _ (𝟙 _) x = a.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    have hb : b.app _ (𝟙 _) x = b.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport ha.symm hb.symm
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)))
      ((e.tensor (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x)).map
        ((truncation 2).map ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y))) (by
          change e.edge.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
            e.edge.app _ (𝟙 _) (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one])).symm

/-- 既存の指定関手同型の一点成分は元の一点評価による同じ指定値の像。 -/
lemma functorIso_app_heq_evaluate {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : X _⦋0⦌) :
    HEq (e.app x) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x)) := by
  let E := (evaluation (hoFunctor.obj X) (hoFunctor.obj Y)).obj (SSet.HomotopyCategory.mk x)
  have h := iso_endpoints_heq ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation X Y).mapIso e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj g)
  have hh := mapIso_heq_of_heq E _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation_obj g) h.symm
  exact hh.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq (functorHomotopyEvaluation_evaluate x) e)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
