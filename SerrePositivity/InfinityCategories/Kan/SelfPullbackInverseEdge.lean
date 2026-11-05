module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FibrationInverseEdge

/-!
概要：自己 pullback の二因子の交換を逆元の辺で比較する。
方針：元の持ち上げの逆向きの辺と逆元の持ち上げを同じ底の上で組にする。
規約：まだ全空間の収縮可能性を要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。二重 loop の変数交換の符号。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：fiber を自己 pullback の第一因子へ含める。
方針：第二因子を全空間の指定基点に固定する。
規約：底の点は p(e)。
使われ方：Goerss–Jardine I §7。連結射の成分を自己 pullback へ送る。 -/
def selfPullbackFiberInclusion {E B : SSet.{u}} (p : E ⟶ B) (e : E _⦋0⦌) :
    KanFiber p (p.app _ e) ⟶ pullback p p :=
  pullback.lift (fiberι p (p.app _ e)) (SSet.const e) (by
    rw [fiberι_comp, SSet.const_comp])

/-- 概要：同じ射の自己 pullback の二因子を交換する。
方針：二つの射影の順序を交換して普遍性により射を作る。
規約：厳密な自己射。
使われ方：Kerodon §3.2.3。二つの三角形の交換の一般的な模型。 -/
def selfPullbackSwap {E B : SSet.{u}} (p : E ⟶ B) : pullback p p ⟶ pullback p p :=
  pullback.lift (pullback.snd p p) (pullback.fst p p) pullback.condition.symm

/-- 概要：逆元の持ち上げの fiber 点と、元の fiber 点を交換した点は辺で結ばれる。
方針：逆向きの辺と逆元の持ち上げは同じ底の辺を持つため pullback へ組にする。
規約：左逆元の積の三角形を明示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5。交換が成分で逆元となることの幾何的な部分。 -/
theorem selfPullback_exists_inverse_edge {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {s t : B.PtSimplex 1 (p.app _ e)}
    (Ls : BoundaryLift p e s) (Lt : BoundaryLift p e t)
    (m : PtSimplex.MulStruct t s .const (0 : Fin 1)) :
    ∃ r : (Δ[1] : SSet.{u}) ⟶ pullback p p,
      stdSimplex.δ (1 : Fin 2) ≫ r = Lt.boundary.map ≫ selfPullbackFiberInclusion p e ∧
      stdSimplex.δ (0 : Fin 2) ≫ r =
        Ls.boundary.map ≫ selfPullbackFiberInclusion p e ≫ selfPullbackSwap p := by
  obtain ⟨K, hKp, hK0, hK1⟩ := exists_inverse_edge p e Ls m
  let r := pullback.lift Lt.map K (Lt.map_comp.trans hKp.symm)
  refine ⟨r, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [r, Category.assoc, pullback.lift_fst, selfPullbackFiberInclusion,
        BoundaryLift.boundary_ι]
      rfl
    · simp only [r, Category.assoc, pullback.lift_snd, selfPullbackFiberInclusion,
        SSet.comp_const, hK1]
  · apply pullback.hom_ext
    · simp only [r, Category.assoc, pullback.lift_fst, selfPullbackSwap,
        pullback.lift_fst, selfPullbackFiberInclusion, pullback.lift_snd, SSet.comp_const]
      exact Lt.face_eq (0 : Fin 2) (by decide)
    · simp only [r, Category.assoc, pullback.lift_snd, selfPullbackSwap,
        pullback.lift_snd, selfPullbackFiberInclusion, pullback.lift_fst,
        BoundaryLift.boundary_ι]
      exact hK0

end

end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackFiberInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackFiberInclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackSwap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackSwap := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackSwap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullback_exists_inverse_edge := _root_.SerrePositivity.InfinityCategories.Kan.selfPullback_exists_inverse_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackFiberInclusion._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackFiberInclusion._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackFiberInclusion.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackFiberInclusion.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackSwap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackSwap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackSwap.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.selfPullbackSwap.eq_1
