module
public import SerrePositivity.KST.Fibration.ZeroCategorySRealization
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps
public import SerrePositivity.KST.SConstruction.KanSourceCoreMap
public import SerrePositivity.KST.SConstruction.FunctorZeroEvaluation
public import SerrePositivity.KST.SConstruction.ClosedStablePredicate

/-! # 零値完全関手の全自然同値を保持する可縮な実部分複体 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の関手単体集合の零頂点を全て保持し、全自然変換を含む全部分複体。 -/
def zeroFunctorLocus (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj B.obj) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex

/-- 全ての実零値関手は、この同じ全部分複体でも零対象である。 -/
theorem zeroFunctorLocus_allZero (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (v : (zeroFunctorLocus A B) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v := by
  have hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v.val := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v hv.1,
    isTerminalVertex_fullSubcomplex_of_ambient _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v hv.2⟩

instance zeroFunctorLocus_hasZeroVertex (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (zeroFunctorLocus A B) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex ((ihom A.obj).obj B.obj)
  let v := fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z.vertex z.isZero
  exact ⟨⟨v, zeroFunctorLocus_allZero A B v⟩⟩

/-- 元の零値関手と自然変換の全部分複体は、全次元の境界を充填する。 -/
theorem zeroFunctorLocus_isContractibleKan (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroFunctorLocus A B) :=
  allZeroVertices_isContractibleKan _ (zeroFunctorLocus_allZero A B)

instance zeroFunctorLocus_kanComplex (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    KanComplex (zeroFunctorLocus A B) := (zeroFunctorLocus_isContractibleKan A B).kanComplex

/-- 零値関手は完全なので、同じ全単体を完全関手の部分複体へ含める。 -/
def zeroFunctorLocusToExact (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    zeroFunctorLocus A B ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex A B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj B.obj) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex).ι (by
      intro v
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A.obj B.obj).symm v.val
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
      have hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :=
        he.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      exact isExact_of_zero_values F (fun a => by
        have h := isZeroVertex_evaluateFunctorAt hz a
        rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h))

/-- 元の関手単体集合への包含は、選び直さず同じ全単体を回収する。 -/
theorem zeroFunctorLocusToExact_inclusion (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    zeroFunctorLocusToExact A B ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj B.obj) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 全自然変換が可逆な実零値部分複体を、元の完全関手の Kan Hom へ含める。 -/
def zeroFunctorLocusToStableHom (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    zeroFunctorLocus A B ⟶ (A ⟶[SSet.{u}] B) :=
  kanSourceCoreMap (zeroFunctorLocusToExact A B)

/-- Kan Hom の core を忘れると、同じ元の零値完全関手の全単体に戻る。 -/
theorem zeroFunctorLocusToStableHom_inclusion (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    zeroFunctorLocusToStableHom A B ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι =
      zeroFunctorLocusToExact A B := kanSourceCoreMap_inclusion _

end SerrePositivity.KST.Fibration
