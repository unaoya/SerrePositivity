module

public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteDiagramVertices
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.PrismVertexEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CoconeFamilyVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeReindex

/-!
概要：同じパラメータ上の小さい辺族を、一つの離散図式の全関手族へまとめる。
方針：離散 nerve の各単体の成分を読み、指定成分の元の全単体を返して curry する。
規約：各成分の全図式を厳密に回収し、頂点だけの一致で置き換えない。
使われ方：共通 compact 表示から余積を組み立てるための全図式族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 小さい成分族の元の全図式を、同じ離散形状とパラメータの積上でまとめる。 -/
def discreteArrowFamilyUncurry {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)) ⊗ K ⟶ X where
  app n := ↾fun z ↦ (D (discreteNerveComponent z.1.down)).app n z.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨s⟩, k⟩
    change (D (discreteNerveComponent ((nerve (Discrete B)).map α s))).app m (K.map α k) =
      X.map α ((D (discreteNerveComponent s)).app n k)
    rw [discreteNerveComponent_map]
    exact ConcreteCategory.congr_hom ((D (discreteNerveComponent s)).naturality α) k

/-- 小さい元の辺族を、一つの離散図式の coherent な族へまとめる。 -/
def discreteArrowFamily {B : Type u} {K X : SSet.{u + 1}} (D : B → (K ⟶ X)) :
    K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete B)))).obj X :=
  curry (discreteArrowFamilyUncurry D)

/-- 全関手族の指定成分での評価は、指定した元の全図式に厳密に等しい。 -/
lemma discreteArrowFamily_evaluate {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (b : B) :
    discreteArrowFamily D ≫ evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk b))) =
      D b := by
  rw [discreteArrowFamily, curry_evaluateFunctorAt_vertex]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro k
  change (D (discreteNerveComponent
    (PinchedHom.constant (nerveVertex (Discrete.mk b)) n))).app _ k = (D b).app _ k
  rfl

/-- 全成分をまとめる操作は、元のパラメータの前合成と厳密に交換する。 -/
lemma discreteArrowFamily_precomp {B : Type u} {J K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (r : J ⟶ K) :
    r ≫ discreteArrowFamily D = discreteArrowFamily (fun b ↦ r ≫ D b) := by
  rw [discreteArrowFamily, discreteArrowFamily, ← curry_natural_left]
  congr 1

/-- 同じパラメータ上の全成分の元の余錐を、一つの関手圏内の全余錐にする。 -/
def discreteArrowFamilyCocone {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (c : ∀ b, JoinCocone (D b)) :
    JoinCocone (discreteArrowFamily D) where
  val := discreteArrowFamily (fun b ↦ (c b).val)
  property := by
    rw [discreteArrowFamily_precomp]
    congr 1
    funext b
    exact (c b).property

/-- 全成分の指定余錐が普遍なら、同じ全余錐をまとめた関手圏内の余錐も普遍。 -/
lemma discreteArrowFamilyCocone_isColimit {B : Type u} {K X : SSet.{u + 1}}
    [Quasicategory X] (D : B → (K ⟶ X)) (c : ∀ b, JoinCocone (D b))
    (hc : ∀ b, IsColimitCone (c b)) : IsColimitCone (discreteArrowFamilyCocone D c) := by
  apply isColimitCone_functor_of_pointwise
  rintro ⟨i⟩
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective i
  apply (isColimitCone_iff_of_coconeMap_eq _ (c b.as) ?_).mpr (hc b.as)
  exact discreteArrowFamily_evaluate (fun b ↦ (c b).val) b.as

/-- 元の全余錐をまとめても、各成分の指定頂点を厳密に保持する。 -/
lemma discreteArrowFamilyCocone_apex_evaluate {B : Type u} {K X : SSet.{u + 1}}
    (D : B → (K ⟶ X)) (c : ∀ b, JoinCocone (D b)) (b : B) :
    (evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk b)))).app _
      (discreteArrowFamilyCocone D c).vertex = (c b).vertex := by
  change (evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk b)))).app _
    (SSet.yonedaEquiv (joinInr K Δ[0] ≫ discreteArrowFamily (fun b ↦ (c b).val))) = _
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (joinInr K Δ[0] ≫
    discreteArrowFamily (fun b ↦ (c b).val) ≫
      evaluateFunctorAt (ULift.up (nerveVertex (Discrete.mk b)))) = _
  rw [discreteArrowFamily_evaluate]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
