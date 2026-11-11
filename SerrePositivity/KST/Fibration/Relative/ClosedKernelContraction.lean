module
public import SerrePositivity.KST.Fibration.Relative.ClosedKernelFlags
public import SerrePositivity.KST.Fibration.RelativeDiagramKernel
public import SerrePositivity.KST.Fibration.StableZeroSDiagonalCylinder
public import SerrePositivity.KST.Fibration.WeakStringRelativeCoreRealization

/-!
概要：P 内の全旗の実現は指定零旗を持ち、局所化で可縮。
方針：零圏への相対 S• を全 S• と同定し、既存の実収縮と全旗比較を消費する。
規約：有限旗の pullback 仮定は使わない。使われ方：相対 fiber の底の収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：P 内の全旗の元の実現。
方針：E_P の二重単体集合の対角。規約：F は単回版。
使われ方：可縮な底。 -/
def closedKernelRealization {B : StableModel.{u}} (P : ClosedStablePredicate B) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (closedKernelFlagDiagram P)

/-- 概要：零圏への相対 S の全段は全 S そのもの。
方針：零性による既存の全図式補題。規約：Verdier 仮定なし。
使われ方：同じ実収縮を使うための厳密同型。 -/
lemma closedKernelRelativeS_eq_top {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    relativeSConstruction (closedKernelZeroMap P).hom n = ⊤ :=
  relativeDiagram_eq_top_of_zero _ (sComponentEvaluation (closedStableModel P).carrier n)
    (fun _ _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)

/-- 概要：相対 S_n の包含を順射に持つ全 S_n との同型。
方針：部分複体の標準同型を合成。
規約：同じ単体を保持。使われ方：全 S• の収縮。 -/
def closedKernelRelativeSIso {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    (relativeSConstruction (closedKernelZeroMap P).hom n : SSet.{u}) ≅
      sConstruction n (closedStableModel P).carrier :=
  Subcomplex.eqToIso (closedKernelRelativeS_eq_top P n) ≪≫ Subcomplex.topIso _

/-- 概要：同型の順射は元の包含。
方針：部分複体間の標準射の包含公式。
規約：厳密等号。使われ方：自然性の照合。 -/
lemma closedKernelRelativeSIso_hom {B : StableModel.{u}}
    (P : ClosedStablePredicate B) (n : ℕ) :
    (closedKernelRelativeSIso P n).hom =
      (relativeSConstruction (closedKernelZeroMap P).hom n).ι :=
  Subcomplex.homOfLE_ι (closedKernelRelativeS_eq_top P n).le

/-- 概要：元の相対 S• と全 S• の全単体的同型。
方針：包含による段ごとの同型を束ねる。
規約：全面・全退化。使われ方：指定零点と実収縮の輸送。 -/
def closedKernelRelativeSimplicialIso {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    relativeSimplicialSConstruction (closedKernelZeroMap P).hom ≅
      simplicialSConstruction (closedStableModel P).carrier :=
  NatIso.ofComponents (fun n => closedKernelRelativeSIso P n.unop.len) (by
    intro n m θ
    change _ ≫ (closedKernelRelativeSIso P _).hom =
      (closedKernelRelativeSIso P _).hom ≫ _
    rw [closedKernelRelativeSIso_hom, closedKernelRelativeSIso_hom]
    rfl)

/-- 概要：P の全 S• 対角の同じ一点射は局所化同型。
方針：既存の指定零自己関手の実収縮を局所化へ送る。
規約：始対象の共終性は使用しない。使われ方：全旗の可縮性。 -/
theorem closedKernelFullS_toPoint_isIso {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from
      (simplicialDiagonalFunctor.obj
        (simplicialSConstruction (closedStableModel P).carrier)))) := by
  let A := flagAmbient (closedStableModel P)
  let Q := AnodyneHomotopy.anodyneQ
  let X := simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)
  have he : Q.map (toUnit X ≫ stableZeroSDiagonalPoint A) = Q.map (𝟙 X) :=
    AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (stableZeroSDiagonalContraction A)
  let e : Q.obj X ≅ Q.obj (𝟙_ SSet.{u}) := {
    hom := Q.map (toUnit X)
    inv := Q.map (stableZeroSDiagonalPoint A)
    hom_inv_id := (Q.map_comp _ _).symm.trans (he.trans (Q.map_id _))
    inv_hom_id := (Q.map_comp _ _).symm.trans
      ((congrArg Q.map (isTerminalTensorUnit.hom_ext _ _)).trans (Q.map_id _)) }
  have : IsIso (Q.map (toUnit X)) := e.isIso_hom
  let t := isTerminalTensorUnit.uniqueUpToIso (terminalIsTerminal (C := SSet.{u}))
  have ht : toUnit X ≫ t.hom = terminal.from X := terminal.hom_ext _ _
  change IsIso (Q.map (terminal.from X))
  rw [← ht, Q.map_comp]
  infer_instance

/-- 概要：E_P の元の対角の一点射は局所化同型。
方針：全相対 S• の実現比較と全 S• の実収縮を合成する。
規約：自然性 pullback の仮定なし。使われ方：指定基点の fiber 比較。 -/
theorem closedKernelRealization_toPoint_isIso {B : StableModel.{u}}
    (P : ClosedStablePredicate B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from (closedKernelRealization P))) := by
  let Q := AnodyneHomotopy.anodyneQ
  let e := simplicialDiagonalFunctor.mapIso (closedKernelRelativeSimplicialIso P)
  let c := relativeSWeakStringCoreComparison (closedKernelZeroMap P)
  have : IsIso (Q.map c) := relativeSWeakStringCoreComparison_localized_isIso _
  have : IsIso (Q.map (terminal.from (simplicialDiagonalFunctor.obj
      (relativeSimplicialSConstruction (closedKernelZeroMap P).hom)))) := by
    have ht : e.hom ≫ terminal.from
        (simplicialDiagonalFunctor.obj
          (simplicialSConstruction (closedStableModel P).carrier)) =
        terminal.from (simplicialDiagonalFunctor.obj
          (relativeSimplicialSConstruction (closedKernelZeroMap P).hom)) :=
      terminal.hom_ext _ _
    have := closedKernelFullS_toPoint_isIso P
    have hi : IsIso (Q.map (e.hom ≫ terminal.from _)) := by
      rw [Q.map_comp]
      infer_instance
    exact ht ▸ hi
  have hc : c ≫ terminal.from (closedKernelRealization P) = terminal.from _ :=
    terminal.hom_ext _ _
  have ht : IsIso (Q.map c ≫ Q.map (terminal.from (closedKernelRealization P))) := by
    rw [← Q.map_comp, hc]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp ht

end SerrePositivity.KST.Fibration.Relative
