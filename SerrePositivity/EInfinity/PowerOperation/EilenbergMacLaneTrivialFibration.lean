module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneConePullback
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-!
# Γ の実射影 trivial fibration は全単射 RLP を持つ

DAG XIII §2.2 の Ω 比較への前段。正規化標準単体の実 latching cofibration と
同じ全自然比較を使う。単体集合のモデル構造を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 境界 frame により、指定 Γ の射が全単射に対する持ち上げ性を持つ。 -/
lemma gammaMap_monomorphisms_rlp {M N : Complex A} (p : M ⟶ N)
    (hp : projectiveFibrations A p) [QuasiIso p] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((truncatedDoldKanFunctor A).map p) := by
  let := projectiveModelCategory A
  have : Fibration p := ⟨hp⟩
  have : WeakEquivalence p := ⟨show QuasiIso p from inferInstance⟩
  have h : (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((gammaStandardHom A).map p) := by
    rw [SSet.rlp_monomorphisms]
    intro K L i hi
    rcases hi with ⟨n⟩
    exact SerrePositivity.HomotopyFunctionComplex.boundary_lifting_of_reedyCofibrant
      (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A) n
      (normalizedSimplex_reedyCofibrant A) p
  let e := gammaStandardHomFunctorIso A
  let ea : Arrow.mk ((gammaStandardHom A).map p) ≅
      Arrow.mk ((truncatedDoldKanFunctor A).map p) :=
    Arrow.isoMk (e.app M) (e.app N) (e.hom.naturality p).symm
  exact ((MorphismProperty.monomorphisms SSet.{u}).rlp.arrow_iso_iff ea).mp h

/-- 恒等射の cone の終対象射には、零次数を含む全境界の充填がある。 -/
lemma gammaIdentityCone_terminal_rlp (M : Complex A) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from ((truncatedDoldKanFunctor A).obj (CochainComplex.mappingCone (𝟙 M)))) := by
  have := identityCone_zero_quasiIso A M
  have hp : projectiveFibrations A
      (0 : CochainComplex.mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A)) := by
    intro n y
    refine ⟨0, ?_⟩
    let : Subsingleton ((HomologicalComplex.zero : Complex A).X n) :=
      ModuleCat.subsingleton_of_isZero
      ((HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero
        HomologicalComplex.isZero_zero)
    exact Subsingleton.elim _ _
  have h := gammaMap_monomorphisms_rlp A
    (0 : CochainComplex.mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A)) hp
  let e := (gammaZeroIsTerminal A).uniqueUpToIso terminalIsTerminal
  have he : ((truncatedDoldKanFunctor A).map
      (0 : CochainComplex.mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A))) ≫
        e.hom = terminal.from _ := terminalIsTerminal.hom_ext _ _
  let ea : Arrow.mk ((truncatedDoldKanFunctor A).map
      (0 : CochainComplex.mappingCone (𝟙 M) ⟶ (HomologicalComplex.zero : Complex A))) ≅
      Arrow.mk (terminal.from _) :=
    Arrow.isoMk (Iso.refl _) e (by simpa using he.symm)
  exact ((MorphismProperty.monomorphisms SSet.{u}).rlp.arrow_iso_iff ea).mp h

end SerrePositivity.EInfinity.PowerOperation
