module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor

/-!
# 試験始域の置換と普通の局所化の自然同型

概要：BM 命題 4.1・Hovey §5 の試験始域の置換を局所化で自然に消す。
方針：既存の比較自然変換のすべての成分を反転する。
規約：元の比較射と普通の局所化関手を使う。
使われ方：計算対象への局所化 Hom の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：試験始域の関手的な置換は局所化後に自然に消せる（Hovey §5）。
方針：同じ比較射の擬同型性を普通の局所化で反転する。
規約：元の複体の cofibrancy は不要。
使われ方：前合成の式から試験始域の置換を消す。 -/
def framedLimitProbeLocalizedIso :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ Q ≅ Q := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let Q := (weakEquivalences (Complex A)).Q
  have h (Y : (Complex A)) : IsIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y)) :=
    Localization.inverts Q (weakEquivalences (Complex A)) _
      (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison_quasiIso A Y)
  exact NatIso.ofComponents (fun Y => asIso (Q.map (_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparison A Y))) (by
    intro Y Z f
    exact (Q.map_comp _ _).symm.trans
      ((congrArg Q.map ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans A).naturality f)).trans
        (Q.map_comp _ _)))

end SerrePositivity.ComplexLimits
