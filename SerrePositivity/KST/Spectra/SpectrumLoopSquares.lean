module

public import SerrePositivity.KST.Spectra.SpectrumFiberSquares
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare

/-!
概要：Sp の任意の頂点の loop 四角形を安定性の仮定なしで構成する。
方針：一点スペクトルの始対象性から 0→x を選び、既証の fiber 四角形を取る。
規約：二つの零角と指定した終頂点を保持する。使われ方：HA §1.4.2 の loop と添字移動の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の Sp の任意の頂点に対する実際の loop 四角形。 -/
def loopSquare (x : Sp.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare x := by
  let z := pointZeroVertex.{u}
  let f := Classical.choice (z.isInitial.nonempty_edge x)
  let s := fiberSquare f
  have h (i : Fin 2) := congrArg
    (fun a : Δ[1] ⟶ Sp.{u} ↦ Sp.{u}.δ i (SSet.yonedaEquiv a)) s.right_edge
  have ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 1 = x := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target]
    exact (h 0).trans ((congrArg (fun a : Sp.{u} _⦋1⦌ ↦ Sp.{u}.δ 0 a)
      (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.tgt_eq)
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex s.square 1 0 = z.vertex := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source]
    exact (h 1).trans ((congrArg (fun a : Sp.{u} _⦋1⦌ ↦ Sp.{u}.δ 1 a)
      (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.src_eq)
  exact ⟨s.toZeroTriangle, ht, hz.symm ▸ z.isZero, s.isPullback⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
