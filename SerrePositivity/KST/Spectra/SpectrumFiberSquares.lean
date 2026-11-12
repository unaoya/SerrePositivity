module

public import SerrePositivity.KST.Spectra.SpectrumZeroObject
public import SerrePositivity.KST.Spectra.CoherentCospanLimits

/-!
概要：任意の coherent cospan の実際の引き戻し四角形と、Sp の各辺の fiber 四角形。
方針：構成済みの極限錐を join と正方形の同型で移し、零頂点を片方の始点に用いる。
規約：入力の二辺、fiber の右辺、および零角を保持する。使われ方：HA §1.4.2、Sp の安定性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 任意の coherent cospan に対する具体的な引き戻し四角形。 -/
def pullbackSquare (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare (CoherentPullback.infinityCone p)

/-- 構成した四角形は ∞ 引き戻し。 -/
lemma pullbackSquare_isPullback (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (pullbackSquare p) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (CoherentPullback.infinityCone_isLimit p)

/-- 四角形の底の二辺は指定した元の cospan に厳密に一致する。 -/
lemma pullbackSquare_cospan (p : (horn 2 2 : SSet.{u + 1}) ⟶ Sp.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (pullbackSquare p) = p := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_cospan _

/-- Sp の全ての指定された辺は fiber 四角形を持つ。 -/
lemma sp_fiber_exists {x y : Sp.{u} _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj Sp.{u}) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits CoherentPullback.hasLimit f

/-- 元の辺を右辺として保持する、選択した実際の fiber 四角形。 -/
def fiberSquare {x y : Sp.{u} _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj Sp.{u}) x y) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiberSquare f :=
  Classical.choice (sp_fiber_exists f)

end SerrePositivity.KST.Spectra.OmegaSpectrum
