module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBasesEvaluation
public import SerrePositivity.InfinityCategories.F1.Fibrations.SubterminalFibrationClassification

/-!
概要：実際の straightening の一点を底とする場合の分類同値。
方針：関手圏の一点評価の厳密な同型と、fiber 評価への全対象の比較を使う。
規約：一般の底の充満忠実性は別の工程。分類写像自体を固定して検証する。
使われ方：一般の分類を底の単体から組み立てる際の零次元の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 各次数で高々一点の始域に頂点があれば、関手圏のその頂点での評価は厳密な同型。 -/
def subterminalFunctorEvaluationIso {B : SSet.{u}}
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) (X : SSet.{u}) :
    (ihom B).obj X ≅ X where
  hom := evaluateFunctorAt b
  inv := curry (snd B X)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    change X.map α (F.app n (𝟙 n) (PinchedHom.constant b n.unop.len)) = F.app d α x
    have h := ConcreteCategory.congr_hom (F.naturality α (𝟙 n))
      (PinchedHom.constant b n.unop.len)
    change F.app d ((𝟙 n) ≫ α) (B.map α (PinchedHom.constant b n.unop.len)) =
      X.map α (F.app n (𝟙 n) (PinchedHom.constant b n.unop.len)) at h
    simpa only [Category.id_comp, Subsingleton.elim x
      (B.map α (PinchedHom.constant b n.unop.len))] using h.symm
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change X.map (𝟙 n) x = x
    exact X.map_id_apply n x

/-- 一点上では、実際の分類写像自体が充満忠実。 -/
lemma leftStraighteningInfinityMap_isFullyFaithful_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsFullyFaithful (leftStraighteningInfinityMap B) := by
  have (n : SimplexCategoryᵒᵖ) :
      Subsingleton (((SSet.uliftFunctor.{u + 1, u}).obj B).obj n) :=
    inferInstanceAs (Subsingleton (ULift.{u + 1} (B.obj n)))
  have he : IsFullyFaithful (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj B) (Y := SpaceInfinity.{u}) (ULift.up b)) :=
    (qCatEquivalenceOfIso (subterminalFunctorEvaluationIso
      (B := (SSet.uliftFunctor.{u + 1, u}).obj B) (ULift.up b) SpaceInfinity.{u})).isFullyFaithful
  exact he.cancel_right ((leftStraighteningInfinityMap_evaluateIso b).isFullyFaithful_iff.mpr
    (leftFibrationInfinityFiberEvaluation_isFullyFaithful_of_subterminal b))

/-- 一点上では、実際の分類写像自体が quasicategory の同値。 -/
lemma leftStraighteningInfinityMap_isQCatEquivalence_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    IsQCatEquivalence (leftStraighteningInfinityMap B) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (leftStraighteningInfinityMap_isFullyFaithful_of_subterminal b)
    (leftStraighteningInfinityMap_isEssentiallySurjective B)

/-- 一点上の分類同値の順方向を実際の straightening に固定したデータ。 -/
def leftStraighteningInfinitySubterminalEquivalence
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    QCatEquivalence (LeftFibrationInfinity B)
      (SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj B)) :=
  (leftStraighteningInfinityMap_isQCatEquivalence_of_subterminal b).choose

/-- 標準零単体上の分類同値。順方向は実際の straightening 写像。 -/
def leftStraighteningInfinityPointEquivalence :
    QCatEquivalence (LeftFibrationInfinity (Δ[0] : SSet.{u}))
      (SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[0] : SSet.{u}))) := by
  have (n : SimplexCategoryᵒᵖ) : Subsingleton ((Δ[0] : SSet.{u}).obj n) := ⟨fun x y ↦ by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega⟩
  exact leftStraighteningInfinitySubterminalEquivalence (stdSimplex.obj₀Equiv.symm (0 : Fin 1))

end SerrePositivity.InfinityCategories
