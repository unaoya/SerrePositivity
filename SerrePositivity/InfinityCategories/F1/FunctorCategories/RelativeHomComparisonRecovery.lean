module

public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorActionEvaluation

/-!
概要：表現可能な相対 Hom の豊穣比較から実際の底上の射を回収する。
方針：表現する対象の恒等射で評価し、全 Hom の自然性で各成分を復元する。
規約：ここでは strict な豊穣比較を扱う。coherent な比較の回収は別工程。
使われ方：標準 Hom の族から全空間側へ戻る評価公式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 表現可能な相対 Hom の比較を恒等射で評価した豊穣射。 -/
def relativeHomComparisonUnit {B : SSet.{u}} {a : Over B} {q : LeftFibrationObject B}
    (η : KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
      (relativeFunctorEnrichedEvaluation a)) :
    𝟙_ SSet.{u} ⟶ relativeFunctorSpace q.val.hom a.hom :=
  relativeFunctorIdentity q.val ≫ η.val q

/-- 恒等射での評価から、底を厳密に保つ実際の射を回収する。 -/
def relativeHomComparisonHom {B : SSet.{u}} {a : Over B} {q : LeftFibrationObject B}
    (η : KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
      (relativeFunctorEnrichedEvaluation a)) : a ⟶ q.val :=
  (relativeFunctorHomEquiv a q.val).symm (relativeHomComparisonUnit η)

/-- 比較の全成分は、恒等射で回収した一つの豊穣射との合成で決まる。 -/
lemma relativeHomComparison_component {B : SSet.{u}} {a : Over B}
    {q : LeftFibrationObject B}
    (η : KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
      (relativeFunctorEnrichedEvaluation a)) (r : LeftFibrationObject B) :
    η.val r =
      (λ_ (relativeFunctorSpace r.val.hom q.val.hom)).inv ≫
        (relativeHomComparisonUnit η ⊗ₘ 𝟙 _) ≫ relativeFunctorComposition a q.val r.val := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  have h := congrArg (fun t ↦ t.app n
    ((relativeFunctorIdentity q.val).app n PUnit.unit, f)) (η.property q r)
  change (relativeFunctorComposition a q.val r.val).app n
    ((η.val q).app n ((relativeFunctorIdentity q.val).app n PUnit.unit), f) =
    (η.val r).app n ((relativeFunctorComposition q.val q.val r.val).app n
      ((relativeFunctorIdentity q.val).app n PUnit.unit, f)) at h
  have hi := congrArg (fun t ↦ t.app n f) (relativeFunctorIdentity_comp q.val r.val)
  change (relativeFunctorComposition q.val q.val r.val).app n
    ((relativeFunctorIdentity q.val).app n PUnit.unit, f) = f at hi
  rw [hi] at h
  exact h.symm

/-- 底上の実際の射による前合成は、その豊穣表示との相対合成。 -/
lemma relativeFunctorOverPre_eq_homComposition {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (r : Over B) :
    relativeFunctorOverPre r.hom f =
      (λ_ (relativeFunctorSpace r.hom b.hom)).inv ≫
        (relativeFunctorHomEquiv a b f ⊗ₘ 𝟙 _) ≫ relativeFunctorComposition a b r := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  change (((relativeFunctorOverPre r.hom f).app n s).val.app d α) x =
    (((relativeFunctorComposition a b r).app n
      ((relativeFunctorHomEquiv a b f).app n PUnit.unit, s)).val.app d α) x
  rw [relativeFunctorOverPre_apply, relativeFunctorComposition_apply]
  have hf := congrArg (fun t ↦ ((t.app n PUnit.unit).app d α) x)
    (relativeFunctorHomEquiv_ι f)
  change (((relativeFunctorHomEquiv a b f).app n PUnit.unit).val.app d α) x =
    f.left.app d x at hf
  exact congrArg (fun z ↦ (s.val.app d α) z) hf.symm

/-- 回収した底上の射の前合成は、元の比較の各成分を厳密に回収する。 -/
lemma relativeHomComparisonHom_component {B : SSet.{u}} {a : Over B}
    {q : LeftFibrationObject B}
    (η : KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
      (relativeFunctorEnrichedEvaluation a)) (r : LeftFibrationObject B) :
    relativeFunctorOverPre r.val.hom (relativeHomComparisonHom η) = η.val r := by
  rw [relativeFunctorOverPre_eq_homComposition, relativeHomComparisonHom,
    Equiv.apply_symm_apply]
  exact (relativeHomComparison_component η r).symm

/-- 一つの豊穣比較の全高次の成分は、回収した底上の射の前合成そのもの。 -/
lemma relativeHomComparisonHom_comparison {B : SSet.{u}} {a : Over B}
    {q : LeftFibrationObject B}
    (η : KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
      (relativeFunctorEnrichedEvaluation a)) :
    relativeFunctorOverPreComparison (relativeHomComparisonHom η) = η := by
  apply Subtype.ext
  funext r
  exact relativeHomComparisonHom_component η r

/-- 実際の底上の射による比較を恒等射で評価すると、その同じ射を回収する。 -/
lemma relativeHomComparisonHom_pre {B : SSet.{u}} {a : Over B}
    {q : LeftFibrationObject B} (f : a ⟶ q.val) :
    relativeHomComparisonHom (relativeFunctorOverPreComparison f) = f := by
  apply (relativeFunctorHomEquiv a q.val).injective
  change (relativeFunctorHomEquiv a q.val)
    ((relativeFunctorHomEquiv a q.val).symm
      (relativeHomComparisonUnit (relativeFunctorOverPreComparison f))) = _
  rw [Equiv.apply_symm_apply]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro t
  cases t
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  change (((relativeFunctorOverPre q.val.hom f).app n
    ((relativeFunctorIdentity q.val).app n PUnit.unit)).val.app d α) x = _
  rw [relativeFunctorOverPre_apply]
  have hf := congrArg (fun t ↦ ((t.app n PUnit.unit).app d α) x)
    (relativeFunctorHomEquiv_ι f)
  change (((relativeFunctorHomEquiv a q.val f).app n PUnit.unit).val.app d α) x =
    f.left.app d x at hf
  exact hf.symm

/-- 底上の射と表現可能な相対 Hom の全 Hom に自然な strict 比較の対応。 -/
def relativeHomComparisonEquiv {B : SSet.{u}} (a : Over B) (q : LeftFibrationObject B) :
    (a ⟶ q.val) ≃
      KanEnrichedComparison (relativeFunctorEnrichedEvaluation q.val)
        (relativeFunctorEnrichedEvaluation a) where
  toFun := relativeFunctorOverPreComparison
  invFun := relativeHomComparisonHom
  left_inv := relativeHomComparisonHom_pre
  right_inv := relativeHomComparisonHom_comparison

end SerrePositivity.InfinityCategories
