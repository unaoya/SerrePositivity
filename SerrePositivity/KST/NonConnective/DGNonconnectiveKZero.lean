module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionZero
public import SerrePositivity.KST.NonConnective.DGNonconnectiveK
public import SerrePositivity.KST.Fibration.DGRelativeZeroPreservation

/-!
概要：元の固定 ν が零なら、同じ実逐次余極限の非連結 K 頂点も零。
方針：実懸垂の全反復で ν の零性を保ち、元の loop 座標と整数 π 余極限を使う。
規約：Sp 安定性や全入力関手性を仮定しない。局所化登録の完成は主張しない。
使われ方：K-7 f の preservesZero 欄へ渡す対象別の実証明。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance ncKZeroSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R A))
include hA

/-- 元の同じ実懸垂の全反復は固定 ν の零性を保つ。 -/
theorem dgSuspensionUnconditionalIteration_stableValue_isZero (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgSuspensionUnconditionalIteration R κ hκ A n)) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact dgKappaSuspensionStableValue_isZero R _ _ ih

/-- 同じ元の loop 段の全整数 π 群は零入力で自明。 -/
theorem dgNonconnectiveKStage_pi_subsingleton (n : ℕ) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j) := by
  have hs := Fibration.spectrum_homotopyGroup_subsingleton_of_positive_toPoint
    (dgNonconnectiveKSuspensionK R κ hκ A n)
    (Fibration.dgKInputSpectrum_positive_toPoint_of_zero R _
      (dgSuspensionUnconditionalIteration_stableValue_isZero R κ hκ A hA n)) (j + n)
  let := hs
  exact (dgNonconnectiveKStage_piEquiv R κ hκ A n j).injective.subsingleton

/-- 同じ実逐次余極限の全整数 π 群は零入力で自明。 -/
theorem dgNonconnectiveK_pi_subsingleton (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup (dgNonconnectiveK R κ hκ A) j) :=
  sequentialPi_subsingleton_of_eventually (dgNonconnectiveKDiagram R κ hκ A) j 0
    (fun n _ => dgNonconnectiveKStage_pi_subsingleton R κ hκ A hA n j)

/-- 固定 ν が零なら、元の実非連結 K 自身の Sp 頂点が零。 -/
theorem dgNonconnectiveK_vertex_isZero_of_zero :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgNonconnectiveK R κ hκ A)) :=
  Fibration.spectrum_isZeroVertex_of_homotopyGroup_subsingleton _
    (dgNonconnectiveK_pi_subsingleton R κ hκ A hA)

omit hA in
/-- 全入力関手が同じ実対象値を持てば、零保存欄は元の実非連結 K の零性で埋まる。 -/
theorem dgNonconnectiveK_preservesRelativeZero_of_vertex
    (E : dgKInputInfinity.{u, max (u + 1) v} R ⟶ Sp.{max (u + 1) v})
    (hE : ∀ B : PerfDGInput.{u, max (u + 1) v} R,
      E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgNonconnectiveK R κ hκ B)) :
    PreservesRelativeZeroCategories (dgKInputNu.{u, max (u + 1) v} R) E := by
  intro a ha
  obtain ⟨B, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (PerfDGInput.{u, max (u + 1) v} R)).surjective a
  have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} _⦋0⦌ =>
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject z)) (dgKInputNu_vertex R B)
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B))
  rw [hE B]
  exact dgNonconnectiveK_vertex_isZero_of_zero R κ hκ B (he.mp ha)

end SerrePositivity.KST.NonConnective
