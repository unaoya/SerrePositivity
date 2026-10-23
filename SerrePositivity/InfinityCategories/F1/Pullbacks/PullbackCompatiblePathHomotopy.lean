module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PathCorrectedSquareEdgeCoherence
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

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
namespace SerrePositivity.InfinityCategories

/-- 同じ path の族の prism は、元の指定端点での評価を回収する。 -/
lemma equivalencePathFamily_prism_endpoint {A Y : SSet.{u}}
    (L : A ⟶ equivalencePath Y) (i : Fin 2) :
    prismEndpoint i A ≫ uncurry (L ≫ equivalencePathι Y) =
      L ≫ equivalencePathEndpoint Y i := by
  rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
  rfl

/-- 同じ共有 path を持つ二つの成分の全円柱は、pullback の全円柱へ貼り合う。 -/
def pullbackCompatiblePathHomotopy {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a b : A ⟶ pullback f g) (L : A ⟶ equivalencePath X) (R : A ⟶ equivalencePath Y)
    (hL0 : L ≫ equivalencePathEndpoint X 0 = a ≫ pullback.fst f g)
    (hL1 : L ≫ equivalencePathEndpoint X 1 = b ≫ pullback.fst f g)
    (hR0 : R ≫ equivalencePathEndpoint Y 0 = a ≫ pullback.snd f g)
    (hR1 : R ≫ equivalencePathEndpoint Y 1 = b ≫ pullback.snd f g)
    (h : L ≫ equivalencePathMap f = R ≫ equivalencePathMap g) : SSet.Homotopy a b := by
  have he : (L ≫ equivalencePathι X) ≫ (ihom (Δ[1] : SSet.{u})).map f =
      (R ≫ equivalencePathι Y) ≫ (ihom (Δ[1] : SSet.{u})).map g := by
    have hh := congrArg (fun t ↦ t ≫ equivalencePathι Z) h
    simpa only [Category.assoc, equivalencePathMap_ι] using hh
  have hc := congrArg uncurry he
  simp only [uncurry_natural_right] at hc
  let H := pullback.lift (uncurry (L ≫ equivalencePathι X))
    (uncurry (R ≫ equivalencePathι Y)) hc
  refine
    { h := (β_ A (Δ[1] : SSet.{u})).hom ≫ H
      h₀ := ?_
      h₁ := ?_
      rel := ?_ }
  · apply pullback.hom_ext
    · change (prismEndpoint 0 A ≫ H) ≫ pullback.fst f g = _
      rw [Category.assoc, pullback.lift_fst, equivalencePathFamily_prism_endpoint, hL0]
      rfl
    · change (prismEndpoint 0 A ≫ H) ≫ pullback.snd f g = _
      rw [Category.assoc, pullback.lift_snd, equivalencePathFamily_prism_endpoint, hR0]
      rfl
  · apply pullback.hom_ext
    · change (prismEndpoint 1 A ≫ H) ≫ pullback.fst f g = _
      rw [Category.assoc, pullback.lift_fst, equivalencePathFamily_prism_endpoint, hL1]
      rfl
    · change (prismEndpoint 1 A ≫ H) ≫ pullback.snd f g = _
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
    (a b : A ⟶ pullback f g) (L : A ⟶ equivalencePath X) (R : A ⟶ equivalencePath Y)
    (hL0 : L ≫ equivalencePathEndpoint X 0 = a ≫ pullback.fst f g)
    (hL1 : L ≫ equivalencePathEndpoint X 1 = b ≫ pullback.fst f g)
    (hR0 : R ≫ equivalencePathEndpoint Y 0 = a ≫ pullback.snd f g)
    (hR1 : R ≫ equivalencePathEndpoint Y 1 = b ≫ pullback.snd f g)
    (h : L ≫ equivalencePathMap f = R ≫ equivalencePathMap g) : FunctorIso a b :=
  functorIsoOfSimplicialHomotopy (pullbackCompatiblePathHomotopy f g a b L R
    hL0 hL1 hR0 hR1 h)

end SerrePositivity.InfinityCategories
