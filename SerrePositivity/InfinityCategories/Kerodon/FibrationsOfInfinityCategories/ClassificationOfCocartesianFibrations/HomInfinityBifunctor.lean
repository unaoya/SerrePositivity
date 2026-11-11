module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SSetProductEvaluation

/-!
概要：元の twisted arrow から得た二変数 Hom 関手の両制限・値・curry を明示する。
方針：同じ共同評価を使い、値は元の表現可能前層の値の比較へ戻す。
規約：独立な Hom 図式を選び直さず、混合する全高次単体を保持する。
使われ方：F1-3b、Kerodon 8、HTT 5.1.3。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
variable {C : SSet.{u}} [Quasicategory C]

/-- 同じ二変数 Hom 関手の指定対象対での値は、元の標準右写像空間と同値。 -/
def homInfinityJointValueEquivalence (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x), ULift.up y))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  by
    have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm x), ULift.up y) := by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity]
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetLift_apply,
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply, NatTrans.id_app, ConcreteCategory.id_apply]
    rw [← h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafValueEquivalence x y

/-- 分離前の同じ twisted arrow 分類図式の値も、元の同じ写像空間と同値。 -/
def twistedArrowHomValueEquivalence (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x, y)))).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  homInfinityJointValueEquivalence x y

/-- 第一変数を固定した、元の二変数 Hom の共変な制限。 -/
def homInfinityCovariant (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  lift (SSet.const (ULift.up (SSet.opObjEquiv.symm x)))
    (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C

/-- 同じ共変制限は、元の Yoneda 関手を同じ対象で評価した実際の合成。 -/
lemma homInfinityCovariant_eq_yonedaEvaluation (x : C _⦋0⦌) :
    homInfinityCovariant x = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityEvaluation x := by
  rw [homInfinityCovariant, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ共変制限の値は元の標準写像空間。 -/
def homInfinityCovariantValueEquivalence (x y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((homInfinityCovariant x).app (Opposite.op ⦋0⦌) (ULift.up y))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :=
  by
    have h : (homInfinityCovariant x).app (Opposite.op ⦋0⦌) (ULift.up y) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm x), ULift.up y) := by
      dsimp only [homInfinityCovariant]
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetLift_apply,
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply, NatTrans.id_app, ConcreteCategory.id_apply]
    rw [h]
    exact homInfinityJointValueEquivalence x y

/-- 第一変数に関する反変性を、共変 Hom 関手の図式として curry した同じ共同評価。 -/
def coyonedaInfinityMap (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
    ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C)

/-- 同じ co-Yoneda の全評価は、元の共同 Hom 評価の二変数を交換したもの。 -/
lemma coyonedaInfinityMap_uncurry (C : SSet.{u}) [Quasicategory C] :
    uncurry (coyonedaInfinityMap C) =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C :=
  uncurry_curry _

/-- 同じ co-Yoneda の指定頂点は、元の共同評価の同じ共変制限の図式。 -/
lemma coyonedaInfinityMap_vertex (x : C _⦋0⦌) :
    (coyonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (homInfinityCovariant x) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.functorVertex_uncurry_at_vertex (coyonedaInfinityMap C)
    (ULift.up (SSet.opObjEquiv.symm x))).symm
  rw [coyonedaInfinityMap_uncurry] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
