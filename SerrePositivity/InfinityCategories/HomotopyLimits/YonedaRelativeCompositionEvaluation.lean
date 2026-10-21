module

public import SerrePositivity.InfinityCategories.F1.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorActionEvaluation

/-!
概要：Yoneda の元の恒等点評価と、相対 Hom 全体の第一変数での合成を照合する。
方針：元の相対合成を同じ fiber の点で評価し、普遍的な fiber 作用へ分解する。
規約：通常の射や零単体に制限せず、二つの全相対写像空間の積を保持する。
使われ方：HTT 5.5.8.10、元の有限余積の脚への Yoneda 評価の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の相対合成の指定点評価は、第一の評価と第二の全 fiber 作用の合成に一致する。 -/
lemma relativeFunctorComposition_pointFiberEvaluation {B : SSet.{u}}
    (a b c : Over B) (x : B _⦋0⦌) (v : (vertexFiber a.hom x) _⦋0⦌) :
    relativeFunctorComposition a b c ≫ relativeFunctorFiberHom a.hom c.hom x ≫
        evaluateFunctorAt v =
      ((relativeFunctorFiberHom a.hom b.hom x ≫ evaluateFunctorAt v) ▷
        relativeFunctorSpace c.hom b.hom) ≫
          relativeFunctorFiberEvaluation b.hom c.hom x := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨f, g⟩
  apply Subtype.ext
  rfl

/-- 元の Yoneda 恒等点評価は、任意の中間対象を通る全相対合成と厳密に可換。 -/
lemma canonicalYonedaRelativeComposition_evaluation {E D C : SSet.{u}} [Quasicategory C]
    (p : E ⟶ C.op) [LeftFibration p] (q : D ⟶ C.op) [LeftFibration q]
    (y : C _⦋0⦌) :
    relativeFunctorComposition
        (Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
        (Over.mk q) (Over.mk p) ≫ canonicalYonedaUnstraighteningEvaluation p y =
      (canonicalYonedaUnstraighteningEvaluation q y ▷ relativeFunctorSpace p q) ≫
        relativeFunctorFiberEvaluation q p (SSet.opObjEquiv.symm y) := by
  rw [canonicalYonedaUnstraighteningEvaluation_eq_fiberEvaluation,
    canonicalYonedaUnstraighteningEvaluation_eq_fiberEvaluation]
  exact relativeFunctorComposition_pointFiberEvaluation
    (Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
    (Over.mk q) (Over.mk p) (SSet.opObjEquiv.symm y) (canonicalYonedaIdentityFiber y)

/-- 表現可能な中間対象でも、元の二対象の恒等点評価と全相対合成を保持する。 -/
lemma yonedaRepresentableRelativeComposition_evaluation
    {E C : SSet.{u}} [Quasicategory C] (p : E ⟶ C.op) [LeftFibration p]
    (x y : C _⦋0⦌) :
    relativeFunctorComposition
        (Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity x)))
        (Over.mk (smallLeftUnstraighteningProjection (representablePresheafInfinity y)))
        (Over.mk p) ≫ canonicalYonedaUnstraighteningEvaluation p x =
      (canonicalYonedaUnstraighteningEvaluation
          (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) x ▷
        relativeFunctorSpace p
          (smallLeftUnstraighteningProjection (representablePresheafInfinity y))) ≫
      relativeFunctorFiberEvaluation
        (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) p
        (SSet.opObjEquiv.symm x) :=
  canonicalYonedaRelativeComposition_evaluation p _ x

end SerrePositivity.InfinityCategories.HomotopyLimits
