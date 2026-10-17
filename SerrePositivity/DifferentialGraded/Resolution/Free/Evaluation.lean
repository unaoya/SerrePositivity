module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Units
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 辺のchain mapから任意のdg圏へのpath評価

合成保存を検証する前のHom chain mapを構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

/-- 非空pathを豊穣順の合成で評価する。辺の次数に制約を置かない。 -/
def wordEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) :
    ∀ (p : List D) (x y : D), wordTensor A D K p x y ⟶ (o x ⟶[Complex A] o y)
  | [], x, y => f x y
  | b :: p, x, y => (f x b ⊗ₘ wordEvaluation K o f p b y) ≫ eComp (Complex A) (o x) (o b) (o y)

/-- 恒等pathはdg単位へ、非空pathはwordEvaluationへ送る。 -/
def pathEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) {x y : D} :
    ∀ p : PathIndex D x y, pathTensor A D K p ⟶ (o x ⟶[Complex A] o y)
  | .inl h => by
    rcases h with ⟨h⟩
    subst y
    exact eId (Complex A) (o x)
  | .inr p => wordEvaluation A D E K o f p x y

variable [Small.{u} D]

/-- 全有限pathの直和を、指定したdg圏のHomへ評価するchain map。 -/
def homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    homComplex A D K x y ⟶ (o x ⟶[Complex A] o y) :=
  Sigma.desc (pathEvaluation A D E K o f)

lemma pathInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ homEvaluation A D E K o f x y =
      pathEvaluation A D E K o f p := Sigma.ι_comp_desc _ _

lemma unitInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x : D) :
    unitInclusion A D K x ≫ homEvaluation A D E K o f x x = eId (Complex A) (o x) :=
  pathInclusion_homEvaluation A D E K o f x x (.inl ⟨rfl⟩)

lemma edgeInclusion_homEvaluation (K : ComplexQuiver A D) (o : D → E)
    (f : ∀ x y, K x y ⟶ (o x ⟶[Complex A] o y)) (x y : D) :
    edgeInclusion A D K x y ≫ homEvaluation A D E K o f x y = f x y :=
  pathInclusion_homEvaluation A D E K o f x y (.inr [])

end SerrePositivity.DifferentialGraded.FreeDGCategory
