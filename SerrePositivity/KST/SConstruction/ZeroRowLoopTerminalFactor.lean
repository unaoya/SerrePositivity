module
public import SerrePositivity.KST.SConstruction.TerminalLoopRestriction
public import SerrePositivity.KST.SConstruction.TerminalFiberEquivalence
public import SerrePositivity.KST.SConstruction.ZeroRowLoopComparison

/-! # 元の零行 loop と終点固定 fiber 比較の厳密な分解
概要：元の円からの零行 loop を fiber に含めると、元の収縮による loop 型比較になる。
方針：path 成分を円の商射上の評価で、全空間成分を基点の厳密な式で照合する。
規約：元の射と区間の向きを保つ。使われ方：実際の構造射の随伴へ π 同型を移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open SerrePositivity.SimplicialModel

/-- 元の零行 loop と標準の loop 包含の合成は、元の収縮の fiber 比較に厳密に一致する。 -/
lemma zeroRowLoopComparison_terminalFactor (r : ℕ) (X : StableModel.{u}) :
    zeroRowLoopComparison r X ≫
      (loopToTerminalPathHomotopyFiber (pointedFullIteratedPathKanBoundary r X)).right =
        zeroRowTerminalLoopFiberComparison r X := by
  let f := pointedFullIteratedPathKanBoundary r X
  apply (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback
    (terminalPathStart ((boundaryKanRealizationFunctor r).obj X)) f).hom_ext
  · rw [Category.assoc, ← Under.comp_right, loopToTerminalPathHomotopyFiber_path]
    change _ = terminalPathFamilyFiberMap f (zeroRowPathContraction r X) _ ≫ _
    rw [terminalPathFamilyFiberMap, IsPullback.lift_fst]
    exact loopTerminalRestriction_family ((boundaryKanRealizationFunctor r).obj X)
      (zeroRowLoopComparison r X) (zeroRowBoundaryCylinder r X)
      (zeroRowBoundaryCylinder_one r X) (zeroRowLoopComparison_raw r X)
  · have hp := congrArg Under.Hom.right (loopToTerminalPathHomotopyFiber_projection f)
    change (loopToTerminalPathHomotopyFiber f).right ≫
      (pullback.snd (terminalPathStart ((boundaryKanRealizationFunctor r).obj X)) f).right =
        (0 : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X) ⟶
          ((pointedIteratedPathKanFunctor r).obj X)).right at hp
    rw [Category.assoc, hp, PointedObject.zero_right, ← Category.assoc,
      comp_toUnit, zeroRowTerminalLoopFiberComparison_projection]

/-- 元の零行 loop と実際の loop 包含の合成は正の全反復で局所化同型。 -/
lemma zeroRowLoopComparison_terminalComposite_localized_isIso (r : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (zeroRowLoopComparison (r + 1) X ≫
      (loopToTerminalPathHomotopyFiber
        (pointedFullIteratedPathKanBoundary (r + 1) X)).right)) := by
  rw [zeroRowLoopComparison_terminalFactor]
  exact zeroRowTerminalLoopFiberComparison_localized_isIso r X

end SerrePositivity.KST.SConstruction
