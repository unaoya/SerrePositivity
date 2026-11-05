module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiNaturality
public import SerrePositivity.InfinityCategories.F1.Universe.Homotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
/-!
概要：指定辺をたどる球面円柱の基点移送を宇宙とともに持ち上げる。
方針：元の円柱を持ち上げ、標準単体の宇宙同型で前合成する。
規約：指定辺も元の辺の持ち上げそのものとする。
使われ方：追加宇宙の全基点チャートを元の native 評価空間へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet HomotopyLimits
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {X : SSet.{u}} [KanComplex X]

lemma dgBarCompactPiTransport_ulift (n : ℕ) {x y : X _⦋0⦌} (e : X.Edge x y)
    {a : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup X n y}
    (h : dgBarCompactPiTransport n e a b) :
    dgBarCompactPiTransport n
      (SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{v, u}).obj X)
        (uliftTruncatedEdge.{u, v} e.toTruncated))
      (dgBarCompactUliftPiEquiv.{u, v} X n x a)
      (dgBarCompactUliftPiEquiv.{u, v} X n y b) := by
  obtain ⟨f, g, hf, hg, H, hH⟩ := h
  let H' := functorHomotopyPrecomp (uliftSimplicialHomotopy.{u, v} H)
    (uliftStdSimplexIso.{u, v} (n + 1)).inv
  refine ⟨dgBarCompactPointedSimplexUp f, dgBarCompactPointedSimplexUp g,
    ?_, ?_, H', ?_⟩
  · exact congrArg (dgBarCompactUliftPiEquiv.{u, v} X n x) hf
  · exact congrArg (dgBarCompactUliftPiEquiv.{u, v} X n y) hg
  · ext d s
    have h₀ := congrArg (fun q => q.app d
      (uliftBoundarySimplexDown.{u, v} (n + 1) d s.1, ULift.up s.2.down)) hH
    exact congrArg ULift.up h₀

end SerrePositivity.InfinityCategories
