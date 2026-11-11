module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSequence
public import SerrePositivity.KST.NonConnective.SequentialCandidatePi
public import SerrePositivity.KST.NonConnective.SequentialPi
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOASpectrumComparison

/-!
概要：同じ反復懸垂の実 Sp 余極限へ、元の連結固定 K からの実比較射を作る。
方針：零段は元の K(D) と厳密一致させ、同じ実余極限余錐の元の脚を使う。
規約：非負次数での同型は隣接遷移の同型性に条件付き。その安定化や Ind 比較を主張しない。
使われ方：K-7 d。群だけの比較ではなく元の実 Sp 比較辺の全整数 π 作用を保持する。
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
local instance connectedComparisonSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 指定次数の隣接遷移に条件付きで、同じ実 Sp 余極限の零段の脚はその次数で全単射。 -/
theorem sequentialCandidateInitialLeg_bijective_of_adjacent
    (D : SpectrumSequence.{w}) (j : ℤ)
    (h : ∀ n : ℕ, Function.Bijective (OmegaSpectrum.homotopyMap
      (D.map (homOfLE (X := SequentialIndex.{w}) (Nat.le_succ n))) j)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D ⟨0⟩) j) := by
  rw [sequentialCandidateColimitLeg_pi]
  apply sequentialInjection_bijective_of_stable D j 0
  intro m _hm
  induction m with
  | zero =>
    have he : (homOfLE (X := SequentialIndex.{w}) (Nat.zero_le 0)) = 𝟙 (⟨0⟩ : SequentialIndex.{w}) :=
      Subsingleton.elim _ _
    rw [he, D.map_id, OmegaSpectrum.homotopyMap_id]
    exact Function.bijective_id
  | succ m ih =>
    have he : (homOfLE (X := SequentialIndex.{w}) (Nat.zero_le (m + 1))) =
        (homOfLE (X := SequentialIndex.{w}) (Nat.zero_le m)) ≫
          (homOfLE (X := SequentialIndex.{w}) (Nat.le_succ m)) := Subsingleton.elim _ _
    rw [he, D.map_comp, OmegaSpectrum.homotopyMap_comp]
    exact (h m).comp (ih (Nat.zero_le m))

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (β : ∀ n : ℕ,
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))))

/-- 明示構造辺に条件付きで、同じ native loop 列の零段は元の連結固定 K そのもの。 -/
theorem dgSuspensionNativeSequenceStage_zero :
    dgSuspensionNativeSequenceStage R s A 0 = dgKInputSpectrum R A := rfl

/-- 明示構造辺に条件付きの、元の連結固定 K から同じ実 Sp 余極限への元の脚。 -/
def dgSuspensionConnectedComparison :
    dgKInputSpectrum R A ⟶ dgSuspensionNativeCandidate R s A β :=
  sequentialCandidateColimitLegHom (dgSuspensionNativeSequence R s A β) ⟨0⟩

/-- 明示構造辺に条件付きで、元の実比較射の全一単体は同じ実 Sp 余錐の零段の脚そのもの。 -/
theorem dgSuspensionConnectedComparison_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionConnectedComparison R s A β)).edge =
      (sequentialCandidateColimitLeg (dgSuspensionNativeSequence R s A β) ⟨0⟩).edge := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom
    (sequentialCandidateColimitLeg (dgSuspensionNativeSequence R s A β) ⟨0⟩)
  exact congrArg (fun e => e.edge) he

/-- 明示構造辺と同じ隣接遷移の指定次数の安定化に条件付きで、元の実比較射はその次数で同型。 -/
theorem dgSuspensionConnectedComparison_bijective (j : ℤ)
    (h : ∀ n : ℕ, Function.Bijective
      (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionConnectedComparison R s A β) j) := by
  apply sequentialCandidateInitialLeg_bijective_of_adjacent
  intro n
  rw [dgSuspensionNativeSequence_map_succ]
  exact h n

/-- 明示構造辺と非負次数の隣接安定化に条件付きで、元の連結 K 比較は全非負整数次数で同型。 -/
def dgSuspensionConnectedComparison_nonnegativeEquiv
    (h : ∀ (j : ℤ), 0 ≤ j → ∀ n : ℕ, Function.Bijective
      (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j))
    (j : ℤ) (hj : 0 ≤ j) :
    OmegaSpectrum.homotopyGroup (dgKInputSpectrum R A) j ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionNativeCandidate R s A β) j :=
  MulEquiv.ofBijective (OmegaSpectrum.homotopyMap (dgSuspensionConnectedComparison R s A β) j)
    (dgSuspensionConnectedComparison_bijective R s A β j (h j hj))

/-- 明示した安定化に条件付きで、非負次数比較同型の順方向は元の実 Sp 比較射の作用。 -/
theorem dgSuspensionConnectedComparison_nonnegativeEquiv_apply
    (h : ∀ (j : ℤ), 0 ≤ j → ∀ n : ℕ, Function.Bijective
      (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j))
    (j : ℤ) (hj : 0 ≤ j) (x : OmegaSpectrum.homotopyGroup (dgKInputSpectrum R A) j) :
    dgSuspensionConnectedComparison_nonnegativeEquiv R s A β h j hj x =
      OmegaSpectrum.homotopyMap (dgSuspensionConnectedComparison R s A β) j x := rfl

/-- 明示構造辺に条件付きの、同じ実 Perf の連結 SOA BF K からの元の比較射。 -/
def dgSuspensionSOAConnectedComparison :
    kOmegaSpectrum (stableCategoryModel (dgKInputStableValue R A)) ⟶
      dgSuspensionNativeCandidate R s A β :=
  presentedPerfectDGBFSOASpectrumComparison R A ≫ dgSuspensionConnectedComparison R s A β

/-- 明示構造辺と非負次数の隣接安定化に条件付きで、同じ SOA 連結 K の実比較射も非負次数で同型。 -/
theorem dgSuspensionSOAConnectedComparison_bijective
    (h : ∀ (j : ℤ), 0 ≤ j → ∀ n : ℕ, Function.Bijective
      (OmegaSpectrum.homotopyMap (dgSuspensionNativeSequenceMap R s A β n) j))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgSuspensionSOAConnectedComparison R s A β) j) := by
  rw [dgSuspensionSOAConnectedComparison, OmegaSpectrum.homotopyMap_comp]
  exact (dgSuspensionConnectedComparison_bijective R s A β j (h j hj)).comp
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R A j)

end SerrePositivity.KST.NonConnective
