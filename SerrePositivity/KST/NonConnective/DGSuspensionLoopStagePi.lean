module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSequence
public import SerrePositivity.KST.Spectra.SpectrumNativeLoopComparison
public import SerrePositivity.KST.Spectra.CotensorLoopGroups
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi

/-!
概要：同じ dg 懸垂段の native loop 反復値を、元の固定 K の整数次数移動へ比較する。
方針：指定 loop 四角形と円 cotensor の公開頂点同型を使い、公開整数 π 同型を反復する。
規約：対象別の次数比較。隣接射との自然性・非負次数安定化や供給の存在は別途証明する。
使われ方：K-7 d2 の同じ BF 反復列の段表示。一般 Sp の loop API は新設しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance loopStagePiSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance loopStagePiSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 指定した同じ dg 懸垂 n 段の固定 K に、native loop を m 回作用させた実 BF 値。 -/
def dgSuspensionLoopedStage (n m : ℕ) : OmegaSpectrum.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (((End.of OmegaSpectrum.nativeLoop ^ m).asHom).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n))))

/-- 同じ n 段の m+1 回 loop 値の整数 π は、m 回 loop 値の一つ上の次数と同型。 -/
def dgSuspensionLoopedStage_stepEquiv (n m : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (dgSuspensionLoopedStage R s A n (m + 1)) j ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionLoopedStage R s A n m) (j + 1) := by
  let x := ((End.of OmegaSpectrum.nativeLoop ^ m).asHom).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject x
  have hpow : ((End.of OmegaSpectrum.nativeLoop ^ (m + 1)).asHom).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n))) =
        OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌) x := by
    simp only [pow_succ', End.mul_asHom]
    rfl
  let hX : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌) x)
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) :=
    eqToIso (congrArg HomotopyCategory.mk (congrArg
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object x).symm))
  let e := (eqToIso (congrArg HomotopyCategory.mk hpow)) ≪≫ hX ≪≫
    OmegaSpectrum.nativeLoopVertexIso (OmegaSpectrum.BasedLoop.square X) ≪≫
      (OmegaSpectrum.BasedLoop.circleVertexIso X).symm
  exact ((SpectrumHo.piFunctor j).mapIso e).commGroupIsoToMulEquiv.trans
    (OmegaSpectrum.cotensorLoopHomotopyEquiv X j)

/-- 同じ n 段の m 回 native loop 値の整数 π を、元の固定 K の j+m 次数へ比較する。 -/
def dgSuspensionLoopedStage_piEquiv (n m : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (dgSuspensionLoopedStage R s A n m) j ≃*
      OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + m) := by
  induction m generalizing j with
  | zero =>
      change OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) j ≃*
        OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + 0)
      exact (MulEquiv.cast
        (M := OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
        (add_zero j)).symm
  | succ m ih =>
      have he := (dgSuspensionLoopedStage_stepEquiv R s A n m j).trans (ih (j + 1))
      have hj : j + 1 + (m : ℤ) = j + ((m + 1 : ℕ) : ℤ) := by omega
      exact he.trans (MulEquiv.cast
        (M := OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n))) hj)

/-- 元の BF 反復列の同じ n 段は、元の n 回懸垂 K の j+n 次数を表す。 -/
def dgSuspensionNativeSequenceStage_piEquiv (n : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (dgSuspensionNativeSequenceStage R s A n) j ≃*
      OmegaSpectrum.homotopyGroup (dgKInputSpectrum R (dgSuspensionIteration R s A n)) (j + n) :=
  dgSuspensionLoopedStage_piEquiv R s A n n j

end SerrePositivity.KST.NonConnective
