module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ObjectwiseTrivial
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.WeakFactorizationSystem
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # Reedy model structures from the constructed relative factorizations

The value category is any Mathlib model category. Only ordinary source
factorization is needed. Degree bijectivity is the hypothesis of the
constructed global factorization; in particular Δ and Δop qualify.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  (r : ReedyStructure inverse direct ℕ)
  {C : Type u'} [Category.{v'} C] [ModelCategory C]
  [∀ j, HasColimitsOfShape (LatchingIndex r j) C]
  [∀ j, HasLimitsOfShape (MatchingIndex r j) C]

omit [∀ j, HasColimitsOfShape (LatchingIndex r j) C] in
lemma reedyRight_trivialFibrations_eq : reedyRight r (trivialFibrations C) =
    reedyRight r (fibrations C) ⊓ (weakEquivalences C).functorCategory J := by
  ext F G τ
  exact reedyRight_trivialFibrations_iff r τ

omit [∀ j, HasLimitsOfShape (MatchingIndex r j) C] in
lemma reedyLeft_trivialCofibrations_eq : reedyLeft r (trivialCofibrations C) =
    reedyLeft r (cofibrations C) ⊓ (weakEquivalences C).functorCategory J := by
  ext F G τ
  exact reedyLeft_trivialCofibrations_iff r τ

@[instance_reducible]
def categoryWithFibrations : CategoryWithFibrations (J ⥤ C) := ⟨reedyRight r (fibrations C)⟩

@[instance_reducible]
def categoryWithCofibrations : CategoryWithCofibrations (J ⥤ C) := ⟨reedyLeft r (cofibrations C)⟩

@[instance_reducible]
def categoryWithWeakEquivalences : CategoryWithWeakEquivalences (J ⥤ C) :=
  ⟨(weakEquivalences C).functorCategory J⟩

instance objectwiseWeakEquivalences_twoOutOfThree :
    ((weakEquivalences C).functorCategory J).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg j := (weakEquivalences C).comp_mem (f.app j) (g.app j) (hf j) (hg j)
  of_postcomp f g hg hfg j := (weakEquivalences C).of_postcomp (f.app j) (g.app j) (hg j) (hfg j)
  of_precomp f g hf hfg j := (weakEquivalences C).of_precomp (f.app j) (g.app j) (hf j) (hfg j)

/-- The actual Reedy model category, with objectwise weak equivalences. -/
@[instance_reducible]
def modelCategory (hinj : Function.Injective r.deg) (hsurj : Function.Surjective r.deg) :
    ModelCategory (J ⥤ C) := by
  letI := categoryWithFibrations (C := C) r
  letI := categoryWithCofibrations (C := C) r
  letI := categoryWithWeakEquivalences (J := J) (C := C)
  have : (weakEquivalences (J ⥤ C)).HasTwoOutOfThreeProperty :=
    objectwiseWeakEquivalences_twoOutOfThree
  have : MorphismProperty.IsWeakFactorizationSystem
      (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) := by
    change MorphismProperty.IsWeakFactorizationSystem (reedyLeft r (cofibrations C))
      (reedyRight r (fibrations C) ⊓ (weakEquivalences C).functorCategory J)
    rw [← reedyRight_trivialFibrations_eq r]
    exact weakFactorizationSystem r (cofibrations C) (trivialFibrations C) hinj hsurj
  have : MorphismProperty.IsWeakFactorizationSystem
      (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) := by
    change MorphismProperty.IsWeakFactorizationSystem
      (reedyLeft r (cofibrations C) ⊓ (weakEquivalences C).functorCategory J)
      (reedyRight r (fibrations C))
    rw [← reedyLeft_trivialCofibrations_eq r]
    exact weakFactorizationSystem r (trivialCofibrations C) (fibrations C) hinj hsurj
  exact ModelCategory.mk' (J ⥤ C)

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.9.19" (partial := component) "仮定：抽象モデル圏 A、必要な境界極限と余極限、自然数次数が全単射（Lean が強い特殊形）。結論：実際の Fun(J,A) に objectwise W と相対 latching/matching によるモデル構造を構成し、trivial cofibration/fibration の二交差式も得る。原文の (C)(F)(W)(WC) にこの特殊形で一致する。任意の整礎次数は含まず、末尾の fibration iff (WF) は trivial fibration に読み替えず一致部分から除外する。"] _root_.SerrePositivity.Reedy.modelCategory
attribute [cite HTT "A.2.9.19" (partial := component) "仮定：抽象モデル圏 A、必要な境界極限と余極限、自然数次数が全単射（Lean が強い特殊形）。結論：実際の Fun(J,A) に objectwise W と相対 latching/matching によるモデル構造を構成し、trivial cofibration/fibration の二交差式も得る。原文の (C)(F)(W)(WC) にこの特殊形で一致する。任意の整礎次数は含まず、末尾の fibration iff (WF) は trivial fibration に読み替えず一致部分から除外する。"] _root_.SerrePositivity.Reedy.reedyLeft_trivialCofibrations_eq
attribute [cite HTT "A.2.9.19" (partial := component) "仮定：抽象モデル圏 A、必要な境界極限と余極限、自然数次数が全単射（Lean が強い特殊形）。結論：実際の Fun(J,A) に objectwise W と相対 latching/matching によるモデル構造を構成し、trivial cofibration/fibration の二交差式も得る。原文の (C)(F)(W)(WC) にこの特殊形で一致する。任意の整礎次数は含まず、末尾の fibration iff (WF) は trivial fibration に読み替えず一致部分から除外する。"] _root_.SerrePositivity.Reedy.reedyRight_trivialFibrations_eq
