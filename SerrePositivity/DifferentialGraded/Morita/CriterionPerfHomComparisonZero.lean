module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfHomComparison
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality

/-! # 全 Hom 比較の閉次数零での実際の射の公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 前合成の複体射は閉次数零でも実際の前合成を与える。 -/
lemma criterionPerf_closedHomEquiv_precompose
    (C : Type v) [DGCategory A C] {x y z : ClosedCategory A C}
    (f : x ⟶ y) (g : y ⟶ z) :
    complexMapZeroCycle A (eHomWhiskerRight (Complex A) f z)
      (closedHomEquiv A C y z g) = closedHomEquiv A C x z (f ≫ g) := by
  have h : eHomEquiv (Complex A) g ≫ eHomWhiskerRight (Complex A) f z =
      eHomEquiv (Complex A) (f ≫ g) := by
    rw [eHomWhiskerRight, eHomEquiv_comp, ← Category.assoc, leftUnitor_inv_naturality]
    simp only [Category.assoc, tensorHom_def']
  apply Subtype.ext
  exact congrArg (fun k => (cycleFromUnit _ k).val) h

/-- dg 関手の全 Hom 射の閉次数零制限は、その通常関手の射写像。 -/
lemma criterionPerf_closedHomEquiv_map
    {C : Type v} [DGCategory A C] {B : Type w} [DGCategory A B]
    (F : DGFunctor A C B) {x y : ClosedCategory A C} (f : x ⟶ y) :
    complexMapZeroCycle A (F.map x y) (closedHomEquiv A C x y f) =
      closedHomEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) := by
  apply Subtype.ext
  exact (cycleFromUnit_postcomp _ _).symm

variable (D : Type v) [DGCategory A D] (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D)

/-- 全 Hom 比較は増強と kernel の左作用の実際の合成を与える。 -/
lemma criterionPerfHomComparison_closedCycle {d d' : ClosedCategory A D} (f : d ⟶ d')
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    complexMapZeroCycle A (criterionPerfHomComparison A D E P d d' R)
      (closedHomEquiv A D d d' f) =
      closedHomEquiv A (RightModule A E) R.obj (criterionPerfColumn A D E P d')
        (R.π ≫ P.toFunctor.onClosed.map f) := by
  change complexMapZeroCycle A (eHomWhiskerRight (Complex A) R.π _)
    (complexMapZeroCycle A (P.toFunctor.map d d') (closedHomEquiv A D d d' f)) = _
  rw [criterionPerf_closedHomEquiv_map]
  exact criterionPerf_closedHomEquiv_precompose A (RightModule A E) R.π
    (P.toFunctor.onClosed.map f)

/-- 列の導来射を計算する同値の下で、比較の H⁰ 写像は実際の左作用の局所化。 -/
lemma criterionPerfHomComparison_homology_zero {d d' : ClosedCategory A D} (f : d ⟶ d')
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        ((moduleToDerived A E).map (P.toFunctor.onClosed.map f)) =
      homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f)) := by
  rw [complexZeroHomologyClass_naturality, criterionPerfHomComparison_closedCycle]
  change moduleProjectiveDerivedHomologyEquiv A E R.projective _
    ((moduleToDerived A E).map R.π ≫ (moduleToDerived A E).map (P.toFunctor.onClosed.map f)) = _
  rw [← CategoryTheory.Functor.map_comp, moduleProjectiveDerivedHomologyEquiv_map]
  rfl

end SerrePositivity.DifferentialGraded.Morita
