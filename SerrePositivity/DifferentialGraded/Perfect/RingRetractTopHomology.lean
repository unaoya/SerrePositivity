module
public import SerrePositivity.DifferentialGraded.Perfect.RingRetract

/-! # 有界有限射影複体の導来retractの最上ホモロジー

上端ではcyclesが項そのものなので有限生成性を使える。一般の次数のホモロジーに
有限生成性を仮定するものではなく、Noetherian性・coherent性は不要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

lemma finiteModule_of_retract {M N : ModuleCat.{u} A} (a : Retract M N) [Module.Finite A N] :
    Module.Finite A M :=
  Module.Finite.of_surjective a.r.hom (fun x =>
    ⟨a.i.hom x, congrArg (fun f => f.hom x) a.retract⟩)

lemma ringComplex_topHomology_finite (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0) :
    Module.Finite A (P.homology n) := by
  let e := P.iCyclesIso n (n + 1) (by simp) hd
  let : Module.Finite A (P.cycles n) := Module.Finite.equiv e.toLinearEquiv.symm
  exact Module.Finite.of_surjective (P.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective (P.homologyπ n)).1 inferInstance)

def ringComplexDerivedHomologyIso (P : Complex A) (n : ℤ) :
    (moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj
        ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) ≅ P.homology n :=
  eqToIso (congrArg (fun F => F.obj ((complexToRingModule A).obj P))
    (moduleDerivedHomology_fac A PUnit.{1} PUnit.unit n)) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).mapIso
        ((complexToRingModuleEvaluationIso A).app P)

lemma ringDerivedRetract_topHomology_finite (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0)
    {X : DerivedModuleCategory A PUnit.{1}}
    (a : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    Module.Finite A ((moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj X) := by
  let := ringComplex_topHomology_finite A P n hd
  exact finiteModule_of_retract A
    ((a.map (moduleDerivedHomology A PUnit.{1} PUnit.unit n)).trans
      (Retract.ofIso (ringComplexDerivedHomologyIso A P n)))

lemma ringDerivedRetract_topHomology_finite_of_strictlyPerfect (P : Complex A)
    (hP : strictlyPerfectComplex A P) (n : ℤ) [P.IsStrictlyLE n]
    {X : DerivedModuleCategory A PUnit.{1}}
    (a : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    Module.Finite A ((moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj X) := by
  let := (hP.2 n).1
  exact ringDerivedRetract_topHomology_finite A P n
    ((P.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _) a

end SerrePositivity.DifferentialGraded
