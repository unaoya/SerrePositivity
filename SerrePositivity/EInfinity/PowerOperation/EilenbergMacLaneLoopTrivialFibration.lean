module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneConeContractibility
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-!
# loop Γ の実射影 trivial fibration と恒等 cone の全境界充填

DAG XIII §2.2 の Ω 比較への前段。実際のシフト射の Γ の持ち上げ性を内部 Hom へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma gammaLoopMap_monomorphisms_rlp {M N : Complex A} (p : M ⟶ N)
    (hp : projectiveFibrations A p) [QuasiIso p] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((gammaLoopFunctor A).map p).right := by
  have hs : projectiveFibrations A (p⟦(1 : ℤ)⟧') := by
    intro n
    exact hp (n + 1)
  exact KST.Spectra.PointedMapping.post_rlp_monomorphisms
    PointedSimplicialSet.circle.{u} ((gammaPointedFunctor A).map (p⟦(1 : ℤ)⟧'))
      (gammaMap_monomorphisms_rlp A _ hs)

lemma gammaLoopIdentityCone_terminal_rlp (M : Complex A) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from ((gammaLoopFunctor A).obj (mappingCone (𝟙 M))).right) := by
  have := identityCone_zero_quasiIso A M
  have hp : projectiveFibrations A
      (0 : mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A)) := by
    intro n y
    let : Subsingleton ((HomologicalComplex.zero : Complex A).X n) :=
      ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero
          HomologicalComplex.isZero_zero)
    exact ⟨0, Subsingleton.elim _ _⟩
  exact terminal_rlp_of_terminalComparison _
    (gammaLoopMap_monomorphisms_rlp A
      (0 : mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A)) hp)
    (gammaLoopZeroIsTerminal A)

end SerrePositivity.EInfinity.PowerOperation
