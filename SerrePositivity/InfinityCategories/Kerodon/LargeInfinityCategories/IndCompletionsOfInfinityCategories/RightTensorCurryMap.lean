module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：右因子を内部 Hom へ移す curry を、全関手空間の射として扱う。
方針：因子交換と既存の全 curry を合成し、元の形状制限との自然性を計算する。
規約：全次数の図式と変換を保持。使われ方：固定円柱境界を全図式の余錐へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の右因子を内部 Hom へ移す、全関手空間上の curry。 -/
def rightTensorCurryMap (A K X : SSet.{u}) :
    (ihom (A ⊗ K)).obj X ⟶ (ihom A).obj ((ihom K).obj X) :=
  (pre (β_ K A).hom).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap K A X

/-- 元の全写像は、同じ因子交換後の curry の頂点へ厳密に送られる。 -/
lemma rightTensorCurryMap_vertex {A K X : SSet.{u}} (f : A ⊗ K ⟶ X) :
    (rightTensorCurryMap A K X).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry ((β_ K A).hom ≫ f)) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap K A X).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((β_ K A).hom ≫ f)) = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex _

/-- 元の第一因子の全形状の制限は、同じ全 curry と厳密に可換。 -/
lemma rightTensorCurryMap_source {A B K X : SSet.{u}} (f : A ⟶ B) :
    (pre (f ▷ K)).app X ≫ rightTensorCurryMap A K X =
      rightTensorCurryMap B K X ≫ (pre f).app ((ihom K).obj X) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro k β
  apply ConcreteCategory.hom_ext
  intro t
  change (s.app k (α ≫ β)) (f.app k (A.map β a), t) =
    (s.app k (α ≫ β)) (B.map β (f.app m a), t)
  exact congrArg (fun b ↦ (s.app k (α ≫ β)) (b, t))
    (ConcreteCategory.congr_hom (f.naturality β) a)

/-- 同じ右因子の curry は、元の形状制限に対して全射の等式として自然。 -/
lemma rightTensorCurry_precomp {A B K X : SSet.{u}} (f : A ⟶ B) (c : B ⊗ K ⟶ X) :
    f ≫ curry ((β_ K B).hom ≫ c) =
      curry ((β_ K A).hom ≫ (f ▷ K) ≫ c) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
