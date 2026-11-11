module
public import SerrePositivity.KST.NonConnective.DGSuspensionStageEquivalence
public import SerrePositivity.KST.NonConnective.DGSuspensionRelativeRoofSequence
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionOriginalStructure
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFConnectivity

/-!
概要：全段の実相対 K 四角形が Sp 引き戻しである場合の、同じ反復候補の帰結を監査する。
方針：同じ構造辺の可逆性を loop 反復と実 BF 遷移へ送り、元の余錐の脚で検出する。
規約：全段の明示屋根・指定 Perf 同値・Sp 引き戻し性に条件付き。一般の供給の存在は主張しない。
使われ方：K-7 d の安定化範囲の確認。非負次数の比較と全整数同値を混同しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance roofStabilizationSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance roofStabilizationHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (ρ : ∀ n, DGKappaSuspensionRelativeRoofInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (e : ∀ n, StableModelEquivalence
    (stableCategoryModel (dgKInputStableValue R (dgSuspensionIteration R s A n)))
    (stableCategoryModel (dgKInputStableValue R (ρ n).kernel)))
  (h : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((ρ n).diagram.square ≫ dgKInputK R))

include h in
/-- 全段の明示屋根・Perf 同値・Sp 引き戻し性に条件付きで、同じ隣接 BF 遷移は全整数 π 同型。 -/
theorem dgSuspensionRoofTransition_piIsomorphism (n : ℕ) :
    OmegaSpectrum.PiIsomorphism (dgSuspensionNativeSequenceMap R s A
      (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e) n) := by
  apply dgSuspensionNativeSequenceMap_piIsomorphism_of_isInvertible
  have hi := (dgKappaSuspensionOriginalStructureMap_isInvertible_iff R
    (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone
      (ρ n) (e n) (Z n)).mpr (h n)
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e n).toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e n).toTruncated)
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionOriginalStructureMap R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone
          (ρ n) (e n) (Z n))).toTruncated) rfl).mpr hi
  have hl := hb.map (End.of OmegaSpectrum.nativeLoop ^ n).asHom
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (dgSuspensionNativeSequenceMap_edge R s A _ n)).mpr
  have he : (dgSuspensionNativeSequenceEdge R s A
      (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e) n).edge =
        ((dgSuspensionRelativeRoofStructureEdge R s A ρ Z e n).map
          (End.of OmegaSpectrum.nativeLoop ^ n).asHom).edge := rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hl

include h in
/-- 全段の明示屋根・Perf 同値・Sp 引き戻し性に条件付きで、元の連結 K 比較は全整数 π 同型。 -/
theorem dgSuspensionRoofConnectedComparison_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgSuspensionConnectedComparison R s A
      (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e)) := by
  intro j
  apply dgSuspensionConnectedComparison_bijective
  intro n
  exact dgSuspensionRoofTransition_piIsomorphism R s A ρ Z e h n j

include h in
/-- 全段の明示屋根・Perf 同値・Sp 引き戻し性に条件付きで、元の連結 K からの実比較辺は可逆。 -/
theorem dgSuspensionRoofConnectedComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionConnectedComparison R s A
      (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e))) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgSuspensionRoofConnectedComparison_piIsomorphism R s A ρ Z e h)

include h in
/-- 全段の明示屋根・Perf 同値・Sp 引き戻し性に条件付きで、同じ候補の全負整数 π は消える。 -/
theorem dgSuspensionRoofCandidate_negative_subsingleton (j : ℤ) (hj : j < 0) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgSuspensionRelativeRoofCandidate R s A ρ Z e) j) := by
  let hs := presentedPerfectDGBFOmegaSpectrum_negative_subsingleton R A j hj
  have hb := dgSuspensionRoofConnectedComparison_piIsomorphism R s A ρ Z e h j
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := hb.surjective x
  obtain ⟨b, rfl⟩ := hb.surjective y
  exact congrArg _ (hs.elim a b)

end SerrePositivity.KST.NonConnective
