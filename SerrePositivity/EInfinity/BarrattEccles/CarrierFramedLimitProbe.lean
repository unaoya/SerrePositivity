module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import SerrePositivity.HomotopicalAlgebra.Generated.Replacement

/-!
# 底の右 frame の錐の関手的な試験始域

概要：Hovey §2.3・§5 の複体の生成分解から右錐の試験始域を構成する。
方針：元の複体の始対象からの射を関手的に cofibrant 置換する。
規約：任意の非有界整数複体で、元の複体の cofibrancy は不要。
使われ方：忘却した右 frame の Kan 錐と元の複体からの局所化 Hom。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：複体の試験始域に使う関手的な生成分解（Hovey §2.3）。
方針：具体的な I・J による小対象分解の存在を使う。
規約：実際の射影モデルを局所的に選ぶ。
使われ方：底の試験始域を全複体に関手的に選ぶ。 -/
def carrierProbeFactorization :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    MorphismProperty.FunctorialFactorizationData
      (cofibrations (Complex A)) (trivialFibrations (Complex A)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A) (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)
  exact MorphismProperty.functorialFactorizationData _ _

/-- 概要：底の右錐の試験始域の置換関手（Hovey §5）。
方針：始対象からの矢印と同じ分解の中間対象関手を合成する。
規約：任意の複体と元の複体射に関手的。
使われ方：底の右錐の始域自然性。 -/
def carrierFramedLimitProbeFunctor : Complex A ⥤ Complex A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact ModelReplacement.initialArrows (Complex A) ⋙ (carrierProbeFactorization A).Z

/-- 概要：元の複体を試す具体的な cofibrant 複体（Hovey §5）。
方針：同じ置換関手の値を取る。
規約：元の複体に追加の条件はない。
使われ方：底の右 frame Hom の fibrant な反対終域。 -/
abbrev carrierFramedLimitProbe (Y : Complex A) : Complex A :=
  (carrierFramedLimitProbeFunctor A).obj Y

/-- 概要：試験始域から元の複体への自然な比較（Hovey §5）。
方針：同じ関手的分解の第二射を使う。
規約：全複体射に自然な元の射。
使われ方：局所化後に試験始域の置換を消す。 -/
def carrierFramedLimitProbeComparison : carrierFramedLimitProbeFunctor A ⟶ 𝟭 (Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact
    { app := fun Y => ((carrierProbeFactorization A).factorizationData (initial.to Y)).p
      naturality := by
        intro Y Z f
        exact (carrierProbeFactorization A).p.naturality
          ((ModelReplacement.initialArrows (Complex A)).map f) }

/-- 概要：底の試験始域は cofibrant（Hovey §2.3・§5）。
方針：始対象からの分解の第一射の cofibration 性を使う。
規約：元の複体の cofibrancy は要求しない。
使われ方：底の右錐の Kan 性と π₀ 比較の具体的条件。 -/
lemma carrierFramedLimitProbe_cofibrant (Y : Complex A) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    IsCofibrant (carrierFramedLimitProbe A Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let d := (carrierProbeFactorization A).factorizationData (initial.to Y)
  change IsCofibrant d.Z
  exact (isCofibrant_iff_of_isInitial d.i initialIsInitial).mpr ⟨d.hi⟩

/-- 概要：試験始域の自然比較は擬同型（Hovey §2.3・§5）。
方針：同じ分解の第二射の自明 fibration 性を使う。
規約：元の比較自然変換の各成分そのもの。
使われ方：元の複体の局所化 Hom を回収する。 -/
lemma carrierFramedLimitProbeComparison_quasiIso (Y : Complex A) :
    QuasiIso ((carrierFramedLimitProbeComparison A).app Y) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact ((carrierProbeFactorization A).factorizationData (initial.to Y)).hp.2

end SerrePositivity.EInfinity.BarrattEccles
