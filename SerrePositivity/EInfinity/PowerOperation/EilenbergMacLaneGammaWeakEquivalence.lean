module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaSmashNaturality
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ModuleNormalizedWeakEquivalence

/-!
# 同じ Γ の弱同値と切断の準同型性

DAG XIII §2.2 のスペクトル忘却の前段。実 Dold–Kan の余単位を保ち、
零次数・全基点を含む既存の Moore 比較へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

open SSet.modelCategoryQuillen in
/-- シフトをまだ入れていない Γ も、同じ dg Hom の線形充填により Kan である。 -/
instance gammaUnderlyingKan (M : Complex A) :
    SSet.KanComplex ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj M) := by
  let e : DifferentialGradedCategories.doldKanHomSpace
      (R := A) (𝟙_ (Complex A)) M ≅ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj M :=
    (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).mapIso (MonoidalClosed.unitIsoSelf (C := Complex A) (X := M))
  exact HomotopicalAlgebra.isFibrant_of_fibration e.inv

/-- 指定された Γ の正規化射は、同じ非負鎖写像と準同型性が同値。 -/
lemma gammaNormalizedMap_quasiIso_iff
    {P Q : ChainComplex (ModuleCat A) ℕ} (f : P ⟶ Q) :
    QuasiIso ((Abelian.DoldKan.N : SimplicialObject (ModuleCat A) ⥤
      ChainComplex (ModuleCat A) ℕ).map
        ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
          SimplicialObject (ModuleCat A)).map f)) ↔ QuasiIso f := by
  let e := (Abelian.DoldKan.equivalence : SimplicialObject (ModuleCat A) ≌
    ChainComplex (ModuleCat A) ℕ).counitIso
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app P) (e.app Q) (e.hom.naturality f).symm)

/-- Γ の台の全基点 π 同型は、同じ smart 切断の準同型性と同値である。 -/
lemma gammaMap_kanPiIsomorphism_iff {M N : Complex A} (f : M ⟶ N) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map f) ↔
    QuasiIso (HomologicalComplex.truncLE'Map f (ComplexShape.embeddingUpIntLE 0)) := by
  have : SSet.KanComplex (moduleUnderlyingSSet (gammaModule A M)) :=
    gammaUnderlyingKan A M
  have : SSet.KanComplex (moduleUnderlyingSSet (gammaModule A N)) :=
    gammaUnderlyingKan A N
  exact (moduleNormalizedMap_quasiIso_iff_kanPiIsomorphism
    ((Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
      SimplicialObject (ModuleCat A)).map
        (HomologicalComplex.truncLE'Map f (ComplexShape.embeddingUpIntLE 0)))).symm.trans
    (gammaNormalizedMap_quasiIso_iff A _)

end SerrePositivity.EInfinity.PowerOperation
