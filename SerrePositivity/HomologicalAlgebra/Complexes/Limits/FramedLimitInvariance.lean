module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimit
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.RealizationInvariance

/-!
# 複体の一般 homotopy 極限の計算関手の擬同型不変性

概要：BM 命題 4.1・Hovey §5.4 の右 frame の end は頂点ごとの擬同型を保つ。
方針：反対圏の重み付き実現に、錐の π₀ による弱同値の検出を適用する。
規約：元の複体に cofibrancy や単体集合のモデル構造を仮定しない。
使われ方：一般 homotopy 極限の右導来普遍性と忘却後の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

attribute [local irreducible] _root_.SerrePositivity.ComplexLimits.rightFrameFamily
attribute [local implicit_reducible] _root_.SerrePositivity.ComplexLimits.rightFrameDiagram _root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：計算関手は頂点ごとの代数の擬同型を擬同型へ送る（BM §1、Hovey §5.4）。
方針：同じ右 frame と射影 cofibrant 重みに対する実現の不変性を使う。
規約：任意の小図式と全図式射、元の複体の cofibrancy は不要。
使われ方：一般 homotopy 極限の計算関手を局所化へ降ろす。 -/
lemma framedLimitFunctor_map_quasiIso {F G : K ⥤ (Complex A)} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k)) :
    QuasiIso ((_root_.SerrePositivity.ComplexLimits.framedLimitFunctor A K).map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.realization_map_frame_weakEquivalence Kᵒᵖ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight K)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant K) (_root_.SerrePositivity.ComplexLimits.rightFrameFactorization A)
    ((_root_.SerrePositivity.ComplexLimits.rightFrameDiagramFamily A K).map f.op)
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (G.obj k.unop))
    (fun k => _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A (F.obj k.unop))
    (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (G.obj k.unop) g)
    (fun k _ _ g => _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A (F.obj k.unop) g)
    (fun k n => _root_.SerrePositivity.ComplexLimits.rightFrame_map_weakEquivalence A (f.app k.unop) (hf k.unop) n)

end SerrePositivity.ComplexLimits
