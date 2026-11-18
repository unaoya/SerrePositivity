module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitConePiZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor

/-!
# 試験始域の定値図式の局所化比較の自然性

概要：BM 命題 4.1・Hovey §5 の試験始域の定値図式の比較を自然同型へ束ねる。
方針：同じ試験始域の比較自然変換を定値図式と普通の局所化へ送る。
規約：既存の constantProbeLocalizedIso の同じ成分を使う。
使われ方：元の定値図式からの Hom の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：試験始域の定値図式の比較は局所化後に自然な同型（Hovey §5）。
方針：元の比較自然変換を同じ定値図式と局所化の合成関手で送る。
規約：元の始域複体の cofibrancy は不要。
使われ方：局所化 Hom の式から試験始域の置換を自然に消す。 -/
def constantProbeLocalizedNatIso :
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (K ⥤ (Complex A))).Q
    _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ Functor.const K ⋙ Q ≅ Functor.const K ⋙ Q := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  let Q := (weakEquivalences (K ⥤ (Complex A))).Q
  let T := Functor.const K ⋙ Q
  exact NatIso.ofComponents (_root_.SerrePositivity.ComplexLimits.constantProbeLocalizedIso A K) (by
    intro Y Z f
    exact (T.map_comp _ _).symm.trans
      ((congrArg T.map ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeComparisonNatTrans A).naturality f)).trans
        (T.map_comp _ _)))

/-- 概要：自然な定値図式の比較同型の成分は既存の同じ比較（Hovey §5）。
方針：自然同型の評価の定義を展開する。
規約：別の局所化同型を選ばない。
使われ方：既存の π₀ 比較に逆の自然性を適用する。 -/
lemma constantProbeLocalizedNatIso_app (Y : (Complex A)) :
    let := _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (_root_.SerrePositivity.ComplexLimits.constantProbeLocalizedNatIso A K).app Y = _root_.SerrePositivity.ComplexLimits.constantProbeLocalizedIso A K Y := rfl

end SerrePositivity.ComplexLimits
