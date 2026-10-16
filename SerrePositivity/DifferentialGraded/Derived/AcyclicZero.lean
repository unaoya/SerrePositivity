module
public import SerrePositivity.DifferentialGraded.Derived.Linear
public import SerrePositivity.DifferentialGraded.Derived.Evaluation

/-! # 主導来圏での零性と評価ホモロジーの消滅 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleAcyclic_zeroTo_quasiIso {N : ModuleCategory A D} (hN : moduleAcyclic A D N) :
    moduleQuasiIso A D (moduleZeroTo A D N) := by
  intro x
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_exactAt _ n ?_).2
  · exact hN x n
  · have hz := (moduleEvaluation A D x).map_isZero (moduleZero_isZero A D)
    exact ExactAt.of_isZero ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero hz)

lemma moduleToDerived_isZero_of_acyclic {N : ModuleCategory A D} (hN : moduleAcyclic A D N) :
    IsZero ((moduleToDerived A D).obj N) :=
  ((moduleToDerived A D).map_isZero (moduleZero_isZero A D)).of_iso
    (moduleDerivedIso A D (moduleZeroTo A D N) (moduleAcyclic_zeroTo_quasiIso A D hN)).symm

lemma moduleDerived_isZero_iff_homology (X : DerivedModuleCategory A D) :
    IsZero X ↔ ∀ (x : D) (n : ℤ), IsZero ((moduleDerivedHomology A D x n).obj X) := by
  constructor
  · intro hX x n
    have hz : IsZero ((moduleDerivedHomology A D x n).obj
        ((moduleToDerived A D).obj (moduleZero A D))) :=
      (HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) n).map_isZero
        ((moduleEvaluation A D x).map_isZero (moduleZero_isZero A D))
    exact hz.of_iso ((moduleDerivedHomology A D x n).mapIso
      (hX.iso ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))))
  · intro hX
    obtain ⟨⟨N⟩⟩ := X
    apply moduleToDerived_isZero_of_acyclic A D
    intro x n
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hX x n)

lemma moduleToDerived_isZero_iff_acyclic (N : ModuleCategory A D) :
    IsZero ((moduleToDerived A D).obj N) ↔ moduleAcyclic A D N := by
  constructor
  · intro hN x n
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      ((moduleDerived_isZero_iff_homology A D _).mp hN x n)
  · exact moduleToDerived_isZero_of_acyclic A D

end SerrePositivity.DifferentialGraded
