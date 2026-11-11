module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeFunctorUnitPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeDomainHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：全余錐族の単位円柱を変数交換して同じ余錐の形状ホモトピーへ戻す。
方針：二重の内部 Hom の同じ全パラメータの座標を比較する。
規約：元の全余錐族を変更しない。
使われ方：選んだ余極限関手の単位の全 Hom 普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：円柱族の二重 curry の交換を元の形状円柱の像へ戻す。
方針：各次数の座標の並べ替えと形状円柱の自然性を使う。
規約：形状円柱と全族を抽象のまま保持する。
使われ方：native な余錐の単位への適用。 -/
lemma coconeUnitReorder_curry_swap {A K B X : SSet.{u}}
    (T : K ⊗ (Δ[1] : SSet.{u}) ⟶ B) (s : A ⟶ (ihom B).obj X) :
    curry (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeUnitReorder K A ≫ (T ▷ A) ≫ uncurry s)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K X).hom =
    curry (T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X s) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro e β
  apply ConcreteCategory.hom_ext
  intro a
  change (s.app e (A.map (𝟙 e) a)).app e (𝟙 e)
    (T.app e (K.map β k, (Δ[1] : SSet.{u}).map (α ≫ β) t)) =
    (s.app e a).app e (𝟙 e) (B.map β (T.app d (k, (Δ[1] : SSet.{u}).map α t)))
  rw [CategoryTheory.Functor.map_id_apply]
  apply congrArg
  have hn := congrArg (fun f : ((K ⊗ (Δ[1] : SSet.{u})).obj d ⟶ B.obj e) ↦
    f (k, (Δ[1] : SSet.{u}).map α t)) (T.naturality β)
  change T.app e (K.map β k,
    (Δ[1] : SSet.{u}).map β ((Δ[1] : SSet.{u}).map α t)) =
      B.map β (T.app d (k, (Δ[1] : SSet.{u}).map α t)) at hn
  simpa only [CategoryTheory.Functor.map_comp_apply] using hn

/-- 概要：全単位の円柱の転置は形状の標準ホモトピーの同じ余錐族での像。
方針：全関手の二重評価を比較する。
規約：全次数のパラメータを保持する。
使われ方：普遍余錐の単位と随伴の指定単位の照合。 -/
lemma coconeFunctorUnitPrism_swap {A K X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).obj X) :
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeFunctorUnitPrism s) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A K X).hom =
      curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeDomainHomotopy K).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) X s) :=
  coconeUnitReorder_curry_swap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeDomainHomotopy K).h s

/-- 概要：全余錐族の単位円柱はパラメータの前合成と可換。
方針：uncurry して、独立した座標の作用を比較する。
規約：元の全族を前合成する。
使われ方：選んだ単位の任意の図式族への制限。 -/
lemma coconeFunctorUnitPrism_precomp {A B K X : SSet.{u}} (i : A ⟶ B)
    (s : B ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).obj X) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeFunctorUnitPrism s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeFunctorUnitPrism (i ≫ s) := by
  apply uncurry_injective
  rw [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeFunctorUnitPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeFunctorUnitPrism,
    uncurry_curry, uncurry_curry, uncurry_natural_left]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
