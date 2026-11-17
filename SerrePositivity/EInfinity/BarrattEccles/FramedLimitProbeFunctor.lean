module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeComparison
public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement

/-!
# 右 frame の錐の試験始域の関手性

概要：BM 命題 4.1・Hovey §5 の既存の試験始域の置換を関手へ束ねる。
方針：始対象からの矢印関手を具体的な分解の中間対象関手へ合成する。
規約：既存の試験始域と比較射をすべての対象で厳密に保持する。
使われ方：右 frame の錐と導来 Hom の始域自然性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：右錐の既存の試験始域の置換関手（Hovey §5）。
方針：始対象からの矢印に同じ自由境界の関手的分解を適用する。
規約：対象と射を新しい置換へ替えない。
使われ方：元の始域代数の射から試験始域の射を作る。 -/
def framedLimitProbeFunctor : (operad A).Algebra ⥤ (operad A).Algebra := by
  let := modelCategory A
  exact ModelReplacement.initialArrows (operad A).Algebra ⋙ (mappingCofibrantFactorization A).Z

/-- 概要：置換関手の値は既存の試験始域（Hovey §5）。
方針：関手的分解と対象ごとの分解の定義を評価する。
規約：同型ではなく同じ元の対象。
使われ方：既存の右錐構成と関手性の照合。 -/
lemma framedLimitProbeFunctor_obj (Y : (operad A).Algebra) :
    (framedLimitProbeFunctor A).obj Y = framedLimitProbe A Y := rfl

/-- 概要：既存の試験始域の比較射は自然変換（Hovey §5）。
方針：関手的分解の第二射の自然性を始対象の矢印へ制限する。
規約：すべての成分は元の比較射そのもの。
使われ方：始域の置換を局所化で消す操作の自然性。 -/
def framedLimitProbeComparisonNatTrans : framedLimitProbeFunctor A ⟶ 𝟭 (operad A).Algebra := by
  let := modelCategory A
  exact
    { app := framedLimitProbeComparison A
      naturality := by
        intro Y Z f
        exact (mappingCofibrantFactorization A).p.naturality
          ((ModelReplacement.initialArrows (operad A).Algebra).map f) }

/-- 概要：試験始域の置換は元の擬同型を保つ（BM 命題 4.1、Hovey §5）。
方針：同じ比較射の自然性と二つのうち三つの性質を使う。
規約：元の始域・終域の cofibrancy は不要。
使われ方：右錐を始域の局所化へ降ろす。 -/
lemma framedLimitProbeFunctor_map_quasiIso {Y Z : (operad A).Algebra}
    (f : Y ⟶ Z) (hf : QuasiIso f.hom) :
    QuasiIso (((framedLimitProbeFunctor A).map f).hom) := by
  let := modelCategory A
  have : WeakEquivalence f := ⟨hf⟩
  have : WeakEquivalence (framedLimitProbeComparison A Y) :=
    ⟨framedLimitProbeComparison_quasiIso A Y⟩
  have : WeakEquivalence (framedLimitProbeComparison A Z) :=
    ⟨framedLimitProbeComparison_quasiIso A Z⟩
  have he := (framedLimitProbeComparisonNatTrans A).naturality f
  change (framedLimitProbeFunctor A).map f ≫ framedLimitProbeComparison A Z =
    framedLimitProbeComparison A Y ≫ f at he
  exact (weakEquivalence_of_postcomp_of_fac he).mem

end SerrePositivity.EInfinity.BarrattEccles
