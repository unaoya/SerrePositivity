module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizationSequential
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.StandardLocalization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CellularNaturalComparison

/-!
概要：任意の単体集合の単体圏からの初頂点写像は、指定辺に関する局所化。
方針：境界の次元帰納、小余積、骨格の pushout、可算骨格の余極限を組み合わせる。
規約：底の quasicategory 性を仮定せず、標的は係数と同じ宇宙で量化する。
使われ方：全単体の共同切断評価を元の底へ coherent に降下する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 任意の底の初頂点写像は、始点を保つ指定辺に関する局所化を表す。 -/
lemma transportSimplexFirstVertexMap_isLocalization (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges B) := by
  let P (X : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges X)
  have hsk : ∀ n (Y : SSet.{u}), P (skeletonOfMono (initial.to Y) n : SSet.{u}) := by
    intro n
    induction n with
    | zero =>
      intro Y
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_iso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso (initial.to Y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_isInitial initialIsInitial)
    | succ n ih =>
      intro Y
      let i : (⊥_ SSet.{u}) ⟶ Y := initial.to Y
      have hb : P (boundary n : SSet.{u}) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_iso
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.initialSkeletonIso (boundary n : SSet.{u}) n).symm (ih _)
      have hBoundaryFamily : P (SSet.relativeCellComplexOfMono.sigmaBoundary i n) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_coproduct
          (fun _ : SSet.relativeCellComplexOfMono.Cell i n ↦ (boundary n : SSet.{u})) (fun _ ↦ hb)
      have hSimplexFamily : P (SSet.relativeCellComplexOfMono.sigmaStdSimplex i n) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_coproduct
          (fun _ : SSet.relativeCellComplexOfMono.Cell i n ↦ (Δ[n] : SSet.{u}))
          (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_standard_isLocalization n)
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_isPushout
        (SSet.relativeCellComplexOfMono.isPushout i n).flip hBoundaryFamily hSimplexFamily (ih Y)
  let r := SSet.relativeCellComplexOfMono (initial.to B)
  have : ∀ n, Mono (r.F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    change Mono (SSet.relativeCellComplexOfMono.r (initial.to B) n)
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_isLocalization_of_sequential_colimit
    (F := r.F) (c := ⟨B, r.incl⟩) r.isColimit (fun n ↦ hsk n B)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
