module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # A locality test computed by a pair of actual source frames

The two frames may be related by any map over the given morphism. Encoding
that map as a parallel-pair diagram makes the common-frame comparison
natural at both endpoints; no global frame family extending these choices
is required.
-/

@[expose] public section
universe v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield.FrameArrowTests

lemma weakSquare_iff {D : Type u'} [Category.{v'} D] (W : MorphismProperty D)
    [W.HasTwoOutOfThreeProperty] {A B A' B' : D}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) (ha : W a) (hb : W b) : W f ↔ W g := by
  constructor
  · intro hf
    exact W.of_precomp _ _ ha (h ▸ W.comp_mem _ _ hf hb)
  · intro hg
    exact W.of_postcomp _ _ hb (h.symm ▸ W.comp_mem _ _ ha hg)

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma mappingTest_iff {X Z : C} (f : X ⟶ Z)
    {A B : SimplexCategory ⥤ C} (t : A ⟶ B)
    (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (b : B ⟶ (Functor.const SimplexCategory).obj Z)
    (h : t ≫ b = a ≫ (Functor.const SimplexCategory).map f)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (ha : ∀ n, weakEquivalences C (a.app n))
    (hb : ∀ n, weakEquivalences C (b.app n)) (Y : C) :
    mappingTest cof fib Y f ↔ weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap t).app ((fibrantTarget fib).obj Y)) := by
  let H : WalkingParallelPair ⥤ C := parallelPair f f
  let P : WalkingParallelPair ⥤ (SimplexCategory ⥤ C) := parallelPair t t
  let aug : P ⟶ H ⋙ Functor.const SimplexCategory := parallelPairHomMk a b h h
  let q := cosimplicialResolutionFamily cof
  let M := FrameOverFunctor.commonObj cof q H P aug
  let T := (fibrantTarget fib).obj Y
  have : IsFibrant T := fibrantTarget_isFibrant fib Y
  have haug (j : WalkingParallelPair) (n : SimplexCategory) :
      weakEquivalences C ((aug.app j).app n) := by
    cases j
    · exact ha n
    · exact hb n
  have hP (j : WalkingParallelPair) :
      reedyLeft simplex (cofibrations C) (initial.to (P.obj j)) := by
    cases j
    · exact hA
    · exact hB
  have hleft (j : WalkingParallelPair) :=
    FrameOverFunctor.homLeft_weakEquivalence cof q H P aug hcof haug (Opposite.op j) T
  have hright (j : WalkingParallelPair) :=
    FrameOverFunctor.homRight_weakEquivalence cof q H P aug hcof hP (Opposite.op j) T
  let l : WalkingParallelPair.zero ⟶ WalkingParallelPair.one := .left
  have sl := congr_app ((FrameOverFunctor.homLeft cof q H P aug).naturality l.op) T
  have sr := congr_app ((FrameOverFunctor.homRight cof q H P aug).naturality l.op) T
  have hl := weakSquare_iff (weakEquivalences SSet.{v}) _ _ _ _ sl
    (hleft .one) (hleft .zero)
  have hr := weakSquare_iff (weakEquivalences SSet.{v}) _ _ _ _ sr
    (hright .one) (hright .zero)
  exact hl.trans hr.symm

end SerrePositivity.Bousfield.FrameArrowTests
