module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRelativeFunctorOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOppositeFibration

/-!
概要：元の相対 Hom を持つ right fibrations の共通解像から、反対の底上の left fibrations への豊穣関手。
方針：対象は射影を反転し、全 Hom には左端射影と相対 Hom の反転同型を使う。
規約：通常の射だけでなく、同じ高次パラメーターの単位・合成を保つ。
使われ方：元の right fibration の ∞ 圏と前層 ∞ 圏の実際の分類写像。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元の right fibration の反転を、反対の底上の left fibration として束ねる。 -/
def rightFibrationOppositeObject {B : SSet.{u}} (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B.op :=
  ⟨Over.mk (SSet.opFunctor.map p.val.hom),
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (SSet.opFunctor.map p.val.hom))⟩

/-- 反転した底上の豊穣単位の包含を、反転した全空間の内部 Hom で表示する。 -/
lemma relativeFunctorOppositeIdentity_ι {B : SSet.{u}} (a : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity (Over.mk (SSet.opFunctor.map a.hom)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left.op).map (SSet.opFunctor.map a.hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map a.hom)) = MonoidalClosed.id a.left.op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity_ι (Over.mk (SSet.opFunctor.map a.hom))

/-- 反転した底上の豊穣合成の包含を、反転した三つの全空間の内部 Hom で表示する。 -/
lemma relativeFunctorOppositeComposition_ι {B : SSet.{u}} (a b c : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (SSet.opFunctor.map a.hom))
      (Over.mk (SSet.opFunctor.map b.hom)) (Over.mk (SSet.opFunctor.map c.hom)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left.op).map (SSet.opFunctor.map c.hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map a.hom)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.left.op).map (SSet.opFunctor.map b.hom))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map a.hom)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom b.left.op).map (SSet.opFunctor.map c.hom))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.opFunctor.map b.hom))) ≫
      MonoidalClosed.comp a.left.op b.left.op c.left.op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι _ _ _

/-- 同じ元の相対 Hom の edgewise 解像上で、反転は単位・合成を保つ豊穣関手。 -/
def rightFibrationOppositeEnriched (B : SSet.{u}) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B.op) where
  obj X := rightFibrationOppositeObject X.val
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite Y.val.val.hom X.val.val.hom
  map_id X := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedIdentity X.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite X.val.val.hom X.val.val.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity (Over.mk (SSet.opFunctor.map X.val.val.hom))
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite_ι,
      relativeFunctorOppositeIdentity_ι X.val.val]
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    rfl
  map_comp X Y Z := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.edgewiseEnrichedComposition X.val Y.val Z.val ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite Z.val.val.hom X.val.val.hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite Y.val.val.hom X.val.val.hom ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite Z.val.val.hom Y.val.val.hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition (Over.mk (SSet.opFunctor.map X.val.val.hom))
        (Over.mk (SSet.opFunctor.map Y.val.val.hom))
        (Over.mk (SSet.opFunctor.map Z.val.val.hom))
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite_ι]
    rw [relativeFunctorOppositeComposition_ι X.val.val Y.val.val Z.val.val]
    rw [← Category.assoc _ _ (MonoidalClosed.comp _ _ _), tensorHom_comp_tensorHom,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRelativeFunctorOpposite_ι]
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
