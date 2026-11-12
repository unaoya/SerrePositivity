module

public import SerrePositivity.EInfinity.PowerOperation.CyclicCoefficientSeed
public import SerrePositivity.EInfinity.Operad.UnitPowers
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# 同じ p 入力の単位での値と指定周期係数模型

DAG XIII Example 2.2.5・Construction 2.2.6 の係数側の比較。
単位上の指定置換作用が恒等であることと同じ単位冪の縮約を使い、
p 入力の単位での値を元の自明係数の複体へ同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex MonoidalCategory
open SerrePositivity.DifferentialGraded
variable {k G : Type u} [CommRing k] [Group G]

local instance powerOperationUnitTrivialFunctorAdditive : (Rep.trivialFunctor k G).Additive where
  map_add := by intros; rfl

/-- 恒等作用を付けた同じ複体と、自明表現関手の像の指定同型。 -/
def representationCochainTrivialIso (K : Complex k) :
    representationCochainComplex (1 : G →* End K) ≅
      ((Rep.trivialFunctor k G).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j h
    simp
    rfl)

/-- 単位のテンソル冪の同じ指定作用は恒等作用。 -/
lemma tensorPowerComplexAction_unit (n : ℕ) (σ : G →* Equiv.Perm (Fin n)) :
    tensorPowerComplexAction (𝟙_ (Complex k)) n σ = 1 := by
  apply MonoidHom.ext
  intro g
  apply End.ext
  exact tensorUnitPower_permutation n (σ g)

variable (p : ℕ) [NeZero p] (k)

/-- 同じ p 入力の単位での値を、同じ自明係数の single 複体へ同定する。 -/
def powerOperationTensorUnitIso :
    (powerOperationTensorInput p k).obj (𝟙_ (Complex k)) ≅
      (singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj
        (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) := by
  change representationCochainComplex
    (tensorPowerComplexAction (𝟙_ (Complex k)) p (powerOperationCyclicPermutation p)) ≅ _
  rw [tensorPowerComplexAction_unit]
  exact representationCochainTrivialIso _ ≪≫
    ((Rep.trivialFunctor k (PowerOperationCyclicGroup.{u} p)).mapHomologicalComplex
      (.up ℤ)).mapIso (tensorUnitPowerIso (Complex k) p) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (Rep.trivialFunctor k (PowerOperationCyclicGroup.{u} p)) (.up ℤ) 0).app
      (ModuleCat.of k k)

/-- 同じ p 入力と周期 Hom の単位での値は、指定係数 Hom 複体と同型。 -/
def powerOperationUnitResolutionHomIso :
    (powerOperationTensorResolutionHom p k).obj (𝟙_ (Complex k)) ≅
      powerOperationCoefficientHomComplex p k :=
  (cyclicResolutionHomFunctor p k).mapIso (powerOperationTensorUnitIso (p := p) (k := k))

end SerrePositivity.EInfinity.PowerOperation
