module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentTotalEquivalence
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakHomotopyInverse

/-!
概要：元の有限 coherent 積の余極限 Kan 模型から、各余極限模型の有限積への比較。
方針：元の全空間比較の Kan 像に元の共通 fiber 積の Kan 比較を合成する。
規約：元の全射影・全空間・置換単位を厳密に保持する。
使われ方：sifted な底上の元の coherent 余極限頂点を持つ native 有限積錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))

/-- 元の有限 coherent 積図式の余極限模型から、元の各余極限模型への指定比較。 -/
def finiteCoherentProductTotalKanComparison :
    F2.coherentDiagramTotalKan (finiteCoherentSpaceProduct n F) ⟶
      nonemptyFiniteSSetProduct n (fun i ↦ F2.coherentDiagramTotalKan (F i)) :=
  F2.continuousKanReplacement.map (finiteCoherentSpaceProductTotalComparison n F) ≫
    finiteCommonFiberProductKanComparison n (fun i ↦ smallLeftUnstraighteningProjection (F i))

/-- 元の Kan 比較の各脚は、元の反復射影の全空間作用の Kan 像。 -/
lemma finiteCoherentProductTotalKanComparison_projection (i : Fin (n + 1)) :
    finiteCoherentProductTotalKanComparison n F ≫
      nonemptyFiniteSSetProjection n (fun j ↦ F2.coherentDiagramTotalKan (F j)) i =
        F2.continuousKanReplacement.map (finiteCoherentSpaceProductTotalProjection n F i) := by
  dsimp only [F2.coherentDiagramTotalKan]
  rw [finiteCoherentProductTotalKanComparison, Category.assoc,
    finiteCommonFiberProductKanComparison_projection, ← Functor.map_comp,
    finiteCoherentSpaceProductTotalComparison_projection]

/-- 元の Kan 比較は元の全空間射影と元の全置換単位に厳密に整合する。 -/
lemma finiteCoherentProductTotalKanComparison_unit :
    F2.continuousKanReplacementUnit.app
      (smallLeftUnstraightening (finiteCoherentSpaceProduct n F)) ≫
      finiteCoherentProductTotalKanComparison n F =
        nonemptyFiniteSSetLift n (fun i ↦ finiteCoherentSpaceProductTotalProjection n F i ≫
          F2.continuousKanReplacementUnit.app (smallLeftUnstraightening (F i))) := by
  dsimp only [F2.coherentDiagramTotalKan]
  apply nonemptyFiniteSSetProduct_hom_ext n _
  intro i
  erw [Category.assoc, finiteCoherentProductTotalKanComparison_projection,
    nonemptyFiniteSSetLift_projection]
  exact (F2.continuousKanReplacementUnit.naturality _).symm

/-- sifted な任意の底上で、元の有限 coherent 余極限 Kan 比較は弱ホモトピー同値。 -/
lemma finiteCoherentProductTotalKanComparison_isWeakHomotopyEquivalence [IsSiftedInfinity B] :
    IsWeakHomotopyEquivalence (finiteCoherentProductTotalKanComparison n F) :=
  (F2.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (finiteCoherentSpaceProductTotalComparison_isWeakHomotopyEquivalence n F)).comp
      (finiteCommonFiberProductKanComparison_homotopyEquivalence n
        (fun i ↦ smallLeftUnstraighteningProjection (F i)) (fun _ ↦ inferInstance)
        ).isWeakHomotopyEquivalence

/-- 同じ元の有限余極限 Kan 比較には、実際の単体的ホモトピー逆がある。 -/
lemma finiteCoherentProductTotalKanComparison_homotopyEquivalence [IsSiftedInfinity B] :
    IsSimplicialHomotopyEquivalence (finiteCoherentProductTotalKanComparison n F) := by
  have : KanComplex (nonemptyFiniteSSetProduct n (fun i ↦ F2.coherentDiagramTotalKan (F i))) :=
    nonemptyFiniteSSetProduct_kanComplex n _ (fun _ ↦ inferInstance)
  exact (finiteCoherentProductTotalKanComparison_isWeakHomotopyEquivalence n F
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
