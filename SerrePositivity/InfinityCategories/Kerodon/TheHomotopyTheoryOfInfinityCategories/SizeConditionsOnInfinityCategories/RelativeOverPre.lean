module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：底上の相対前合成の宇宙移送の自然性と同値性の反映。
方針：全ての単体の入力で前合成を比較し、相対 Hom の宇宙同型の二対三則を使う。
規約：射影は left fibration。底上の比較射自体の同値性は要求しない。
使われ方：大きい宇宙で証明した初頂点引き戻しの同値性を元の宇宙へ反映する。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 元の底上の射を、持ち上げた底上の射として表示する。 -/
def uliftOverMorphism {B : SSet.{u}} {a b : Over B} (f : a ⟶ b) :
    Over.mk ((SSet.uliftFunctor.{v, u}).map a.hom) ⟶
      Over.mk ((SSet.uliftFunctor.{v, u}).map b.hom) :=
  Over.homMk ((SSet.uliftFunctor.{v, u}).map f.left) (by
    change (SSet.uliftFunctor.{v, u}).map f.left ≫
      (SSet.uliftFunctor.{v, u}).map b.hom = (SSet.uliftFunctor.{v, u}).map a.hom
    rw [← Functor.map_comp, f.w])

/-- 相対 Hom の宇宙移送は、元の底上の射による前合成と厳密に可換。 -/
lemma uliftRelativeFunctorMap_overPre {E B : SSet.{u}}
    (p : E ⟶ B) {a b : Over B} (f : a ⟶ b) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap p a.hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap p b.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre ((SSet.uliftFunctor.{v, u}).map p) (uliftOverMorphism f) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 持ち上げた同じ底上の射の前合成が同値なら、元の相対前合成も同値。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_of_ulift
    {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : Over B} (f : a ⟶ b)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre ((SSet.uliftFunctor.{v, u}).map p) (uliftOverMorphism f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p f)).mp
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap.{u, v} p a.hom) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorIso p a.hom)).isQCatEquivalence
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorMap.{u, v} p b.hom) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorIso p b.hom)).isQCatEquivalence
  apply ha.cancel_right
  rw [uliftRelativeFunctorMap_overPre]
  exact hb.comp h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
