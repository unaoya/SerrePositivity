module

public import SerrePositivity.BhattScholze.Perfectoidization.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FinitePresentationComplete
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Prop 2.4.7：元の標準射と実錐の導来 p 完備性

有限性と代数としての有限表示性から加群としての有限表示性を得る。
bounded p 冪 torsion は完備底変換の古典比較で用いる仮定であり、
この導来完備性には不要である。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

include hR in
/-- 原典の有限かつ有限表示な S は、元の R 作用について導来 p 完備。 -/
theorem prop247_source_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R S) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  exact isModuleComplete_of_finitePresentation R (p : R)
    (hR.isModuleComplete R p) (ModuleCat.of R S)

/-- 選択済み perfectoid 化は、元の R 作用について導来 p 完備。 -/
theorem prop247_target_isModuleComplete :
    IsModuleComplete R (p : R) (ModuleCat.of R (Perfectoidization R S p hR)) :=
  (isPerfectoidization_toPerfectoidization R S p hR).1.isModuleComplete_algebra
    R (Perfectoidization R S p hR) p

include hR in
/-- 任意に指定した perfectoid な終域への実射の錐は導来 p 完備。
普遍対象の存在引用を用いない入口。 -/
theorem prop247_cone_isComplete_of_perfectoid_target
    (P : Type u) [CommRing P] [Algebra R P]
    (hP : IsIntegralPerfectoid P p) (f : S →ₗ[R] P) :
    IsComplete R (p : R) (moduleMapCone R f) := by
  apply isComplete_Q_mappingCone R (p : R) (moduleMapSingle R f)
  · exact prop247_source_isModuleComplete R S p hR
  · exact hP.isModuleComplete_algebra R P p

/-- Prop 2.4.7 の実際の標準写像の実導来錐は p 完備。
エタール性、J、g、André 拡大、almost 比較を使わない。 -/
theorem prop247_cone_isComplete :
    IsComplete R (p : R) (BhattScholze.perfectoidizationCone R S p hR) := by
  exact prop247_cone_isComplete_of_perfectoid_target R S p hR
    (Perfectoidization R S p hR) (isPerfectoidization_toPerfectoidization R S p hR).1
    (BhattScholze.perfectoidizationModuleMap R S p hR)

end SerrePositivity.CLMST
