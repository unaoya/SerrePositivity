module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.HomotopyCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelHomotopyAdjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
/-!
概要：同じ実右随伴を、既存 telescope の古典的 RHom と全射に自然に比較する。
方針：一点上の全パラメータ Hom 対応を評価し、同じ左随伴の右随伴の一意性を使う。
規約：全ての射への自然性と、単位・余単位との整合を保持する。
使われ方：一般 kernel の実 RHom と既存の主導来 RHom の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 同じ実右随伴の h は、同じ左随伴の既存 telescope の右随伴と自然同型。 -/
def dgKernelRightAdjoint_homotopyIso (R : Type u) [CommRing R] (D E : Type v)
    [DifferentialGraded.DGCategory R D] [Small.{u} D]
    [DifferentialGraded.DGCategory R E] [Small.{u} E]
    (P : DifferentialGraded.Bimodule R E D) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P)).toFunctor ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelHomotopyRightAdjoint R D E P :=
  Adjunction.rightAdjointUniq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P).toHoAdjunction
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelHomotopyAdjunction R D E P)

/-- 同じ実右随伴の h は、主導来圏の元の kernel RHom と全射に自然同型。 -/
def dgKernelRightAdjoint_classicalIso (R : Type u) [CommRing R] (D E : Type v)
    [DifferentialGraded.DGCategory R D] [Small.{u} D]
    [DifferentialGraded.DGCategory R E] [Small.{u} E]
    (P : DifferentialGraded.Bimodule R E D) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P)).toFunctor ⋙
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHomotopyEquivalence R D).functor ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHomotopyEquivalence R E).functor ⋙
        DifferentialGraded.Morita.kernelDerivedHom R D E
          ((DifferentialGraded.bimoduleToDerived R E D).obj
            (DifferentialGraded.BimoduleCategory.of R E D P)) := by
  let HD := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHomotopyEquivalence R D
  let HE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHomotopyEquivalence R E
  let K := (DifferentialGraded.bimoduleToDerived R E D).obj
    (DifferentialGraded.BimoduleCategory.of R E D P)
  have e : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelRightAdjointCandidate R D E P)).toFunctor ≅
      (HE.functor ⋙ DifferentialGraded.Morita.kernelDerivedHom R D E K) ⋙ HD.inverse := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelHomotopyRightAdjoint, Functor.assoc] using
      dgKernelRightAdjoint_homotopyIso R D E P
  exact CategoryTheory.Iso.compInverseIso (H := HD.symm) e

/-- 同じ右随伴の比較同型は、通常の h 上の指定単位に整合する。 -/
lemma dgKernelRightAdjoint_homotopyIso_unit (R : Type u) [CommRing R] (D E : Type v)
    [DifferentialGraded.DGCategory R D] [Small.{u} D]
    [DifferentialGraded.DGCategory R E] [Small.{u} E]
    (P : DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P).toHoAdjunction.unit ≫
      Functor.whiskerLeft (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor
        (dgKernelRightAdjoint_homotopyIso R D E P).hom =
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelHomotopyAdjunction R D E P).unit :=
  Adjunction.unit_rightAdjointUniq_hom _ _

/-- 同じ右随伴の比較同型は、通常の h 上の指定余単位に整合する。 -/
lemma dgKernelRightAdjoint_homotopyIso_counit (R : Type u) [CommRing R] (D E : Type v)
    [DifferentialGraded.DGCategory R D] [Small.{u} D]
    [DifferentialGraded.DGCategory R E] [Small.{u} E]
    (P : DifferentialGraded.Bimodule R E D) :
    Functor.whiskerRight (dgKernelRightAdjoint_homotopyIso R D E P).hom
        (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).toFunctor ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelHomotopyAdjunction R D E P).counit =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelAdjunction R D E P).toHoAdjunction.counit :=
  Adjunction.rightAdjointUniq_hom_counit _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
