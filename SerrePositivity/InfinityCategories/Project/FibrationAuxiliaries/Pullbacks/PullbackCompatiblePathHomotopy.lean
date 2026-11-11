module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquareEdgeCoherence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：共有頂点で厳密に整合する二つの成分 path を、同じ pullback 上で貼り合わせる。
方針：包含後の全円柱を pullback に持ち上げ、両端を同じ二射影で検査する。
規約：成分 path と共有頂点での等式を保持する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 同じ path の族の prism は、元の指定端点での評価を回収する。 -/
lemma equivalencePathFamily_prism_endpoint {A Y : SSet.{u}}
    (L : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A ≫ uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) =
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y i := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
  rfl

/-- 同じ共有 path を持つ二つの成分の全円柱は、pullback の全円柱へ貼り合う。 -/
def pullbackCompatiblePathHomotopy {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a b : A ⟶ pullback f g) (L : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (R : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y)
    (hL0 : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = a ≫ pullback.fst f g)
    (hL1 : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = b ≫ pullback.fst f g)
    (hR0 : R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = a ≫ pullback.snd f g)
    (hR1 : R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = b ≫ pullback.snd f g)
    (h : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap f = R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g) : SSet.Homotopy a b := by
  have he : (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ (ihom (Δ[1] : SSet.{u})).map f =
      (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y) ≫ (ihom (Δ[1] : SSet.{u})).map g := by
    have hh := congrArg (fun t ↦ t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Z) h
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι] using hh
  have hc := congrArg uncurry he
  simp only [uncurry_natural_right] at hc
  let H := pullback.lift (uncurry (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X))
    (uncurry (R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y)) hc
  refine
    { h := (β_ A (Δ[1] : SSet.{u})).hom ≫ H
      h₀ := ?_
      h₁ := ?_
      rel := ?_ }
  · apply pullback.hom_ext
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) ≫ pullback.fst f g = _
      rw [Category.assoc, pullback.lift_fst, equivalencePathFamily_prism_endpoint, hL0]
      rfl
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) ≫ pullback.snd f g = _
      rw [Category.assoc, pullback.lift_snd, equivalencePathFamily_prism_endpoint, hR0]
      rfl
  · apply pullback.hom_ext
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ≫ pullback.fst f g = _
      rw [Category.assoc, pullback.lift_fst, equivalencePathFamily_prism_endpoint, hL1]
      rfl
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ≫ pullback.snd f g = _
      rw [Category.assoc, pullback.lift_snd, equivalencePathFamily_prism_endpoint, hR1]
      rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 同じ二成分の path が整合すれば、元の pullback 上の二つの射は関手同型。 -/
def pullbackFunctorIsoOfCompatiblePaths {A X Y Z : SSet.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [KanComplex (pullback f g)]
    (a b : A ⟶ pullback f g) (L : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (R : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y)
    (hL0 : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = a ≫ pullback.fst f g)
    (hL1 : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = b ≫ pullback.fst f g)
    (hR0 : R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 0 = a ≫ pullback.snd f g)
    (hR1 : R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y 1 = b ≫ pullback.snd f g)
    (h : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap f = R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (pullbackCompatiblePathHomotopy f g a b L R
    hL0 hL1 hR0 hR1 h)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
