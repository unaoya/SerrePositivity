module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteDiagramVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeFamilyVertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeReindex

/-!
概要：同じパラメータ上の小さい辺族を、一つの離散図式の全関手族へまとめる。
方針：離散 nerve の各単体の成分を読み、指定成分の元の全単体を返して curry する。
規約：各成分の全図式を厳密に回収し、頂点だけの一致で置き換えない。
使われ方：共通 compact 表示から余積を組み立てるための全図式族。

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

/-- 小さい成分族の元の全図式を、同じ離散形状とパラメータの積上でまとめる。 -/
def discreteArrowFamilyUncurry {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⊗ K ⟶ X where
  app n := ↾fun z ↦ (D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent z.1.down)).app n z.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨s⟩, k⟩
    change (D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent ((nerve (Discrete B)).map α s))).app m (K.map α k) =
      X.map α ((D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent s)).app n k)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent_map]
    exact ConcreteCategory.congr_hom ((D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent s)).naturality α) k

/-- 小さい元の辺族を、一つの離散図式の coherent な族へまとめる。 -/
def discreteArrowFamily {B : Type u} {K X : SSet.{u + 1}} (D : B → (K ⟶ X)) :
    K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)))).obj X :=
  curry (discreteArrowFamilyUncurry D)

/-- 全関手族の指定成分での評価は、指定した元の全図式に厳密に等しい。 -/
lemma discreteArrowFamily_evaluate {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (b : B) :
    discreteArrowFamily D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b))) =
      D b := by
  rw [discreteArrowFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro k
  change (D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteNerveComponent
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)) n))).app _ k = (D b).app _ k
  rfl

/-- 全成分をまとめる操作は、元のパラメータの前合成と厳密に交換する。 -/
lemma discreteArrowFamily_precomp {B : Type u} {J K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (r : J ⟶ K) :
    r ≫ discreteArrowFamily D = discreteArrowFamily (fun b ↦ r ≫ D b) := by
  rw [discreteArrowFamily, discreteArrowFamily, ← curry_natural_left]
  congr 1

/-- 同じパラメータ上の全成分の元の余錐を、一つの関手圏内の全余錐にする。 -/
def discreteArrowFamilyCocone {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (c : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (discreteArrowFamily D) where
  val := discreteArrowFamily (fun b ↦ (c b).val)
  property := by
    rw [discreteArrowFamily_precomp]
    congr 1
    funext b
    exact (c b).property

/-- 全成分の指定余錐が普遍なら、同じ全余錐をまとめた関手圏内の余錐も普遍。 -/
lemma discreteArrowFamilyCocone_isColimit {B : Type u} {K X : SSet.{u + 1}}
    [Quasicategory X] (D : B → (K ⟶ X)) (c : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D b))
    (hc : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c b)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (discreteArrowFamilyCocone D c) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.isColimitCone_functor_of_pointwise
  rintro ⟨i⟩
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective i
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isColimitCone_iff_of_coconeMap_eq _ (c b.as) ?_).mpr (hc b.as)
  exact discreteArrowFamily_evaluate (fun b ↦ (c b).val) b.as

/-- 元の全余錐をまとめても、各成分の指定頂点を厳密に保持する。 -/
lemma discreteArrowFamilyCocone_apex_evaluate {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (c : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D b)) (b : B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))).app _
      (discreteArrowFamilyCocone D c).vertex = (c b).vertex := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))).app _
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ discreteArrowFamily (fun b ↦ (c b).val))) = _
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫
    discreteArrowFamily (fun b ↦ (c b).val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk b)))) = _
  rw [discreteArrowFamily_evaluate]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
