module

public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitCones

/-!
# 右 frame の錐の試験始域と元の代数の比較

概要：BM 命題 4.1・Hovey §5 の実際の試験始域の置換射を公開する。
方針：始対象からの具体的な関手的分解の第二射と二つの類の保証を使う。
規約：元の代数には cofibrancy を仮定しない。
使われ方：両 frame の錐比較と元の定値図式からの導来 Hom の回収。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra

variable (A : Type u) [CommRing A]

/-- 概要：錐の実際の試験始域から元の代数への比較射（Hovey §5）。
方針：始対象からの同じ自由境界分解の第二射を取る。
規約：既存の試験始域を変更しない。
使われ方：置換された定値図式から元の定値図式へ戻す。 -/
def framedLimitProbeComparison (Y : (operad A).Algebra) : framedLimitProbe A Y ⟶ Y := by
  let := modelCategory A
  exact ((mappingCofibrantFactorization A).factorizationData (initial.to Y)).p

/-- 概要：錐の試験始域の比較射は擬同型（BM 命題 4.1）。
方針：選んだ分解の自明 fibration の保証を使う。
規約：底の元の複体射の擬同型性。
使われ方：局所化後に試験始域の置換を消す。 -/
lemma framedLimitProbeComparison_quasiIso (Y : (operad A).Algebra) :
    QuasiIso (framedLimitProbeComparison A Y).hom := by
  let := modelCategory A
  exact ((mappingCofibrantFactorization A).factorizationData (initial.to Y)).hp.2

/-- 概要：錐の選んだ試験始域は cofibrant（BM 命題 4.1）。
方針：始対象からの分解の第一射が cofibration であることを使う。
規約：元の代数の cofibrancy を入力にはしない。
使われ方：混合 Hom の右比較の条件を具体的に供給する。 -/
lemma framedLimitProbe_cofibrant (Y : (operad A).Algebra) :
    let := modelCategory A
    IsCofibrant (framedLimitProbe A Y) := by
  let := modelCategory A
  let d := (mappingCofibrantFactorization A).factorizationData (initial.to Y)
  change IsCofibrant d.Z
  exact (isCofibrant_iff_of_isInitial d.i initialIsInitial).mpr ⟨d.hi⟩

end SerrePositivity.EInfinity.BarrattEccles
