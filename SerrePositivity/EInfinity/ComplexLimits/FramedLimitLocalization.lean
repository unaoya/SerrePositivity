module

public import SerrePositivity.EInfinity.ComplexLimits.FramedLimitInvariance
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramModel

/-!
# 定値図式と具体的な極限計算関手の普通の局所化への降下

概要：BM 命題 4.1・Hovey §1.3 の弱同値不変な二つの関手を普通の局所化へ降ろす。
方針：元の定値図式と元の計算関手の弱同値保存を局所化の普遍性へ入力する。
規約：値や射を別の導来候補へ置き換えない。
使われ方：導来 Hom 同値から局所化圏上の随伴を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：局所化へ続く定値図式関手は元の弱同値を反転（Hovey §1.3）。
方針：定値図式の全成分が同じ擬同型であることを使う。
規約：具体的な代数モデルと図式モデルを局所的に選ぶ。
使われ方：定値図式関手を普通の局所化へ降ろす。 -/
lemma constantDiagram_inverts :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let QD := (weakEquivalences (K ⥤ (Complex A))).Q
    (weakEquivalences (Complex A)).IsInvertedBy (Functor.const K ⋙ QD) := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro Y Z f hf
  have hq : QuasiIso f := hf
  exact Localization.inverts (weakEquivalences (K ⥤ (Complex A))).Q
    (weakEquivalences (K ⥤ (Complex A)))
    ((Functor.const K).map f)
    ((BarrattEccles.CarrierDiagram.weakEquivalence_iff A K ((Functor.const K).map f)).mpr (fun _
      => hq)).mem

/-- 概要：元の計算関手は図式の弱同値を局所化で反転（Hovey §1.3）。
方針：既存の計算関手の擬同型保存を同じ局所化へ送る。
規約：元の始域の cofibrancy は不要。
使われ方：具体的な極限計算関手の局所化への降下。 -/
lemma framedLimit_inverts :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    (weakEquivalences (K ⥤ (Complex A))).IsInvertedBy (framedLimitFunctor A K ⋙ Q) := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  dsimp only
  intro F G f hf
  exact Localization.inverts (weakEquivalences (Complex A)).Q
    (weakEquivalences (Complex A))
    ((framedLimitFunctor A K).map f) (framedLimitFunctor_map_quasiIso A K f
      ((BarrattEccles.CarrierDiagram.weakEquivalence_iff A K f).mp ⟨hf⟩))

/-- 概要：普通の局所化圏上の定値図式関手（Hovey §1.3）。
方針：元の定値図式関手を同じ弱同値の局所化で因子化する。
規約：局所化は具体的な二つのモデルの普通の局所化。
使われ方：一般極限の導来随伴の左関手。 -/
def localizedConstantDiagram :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (weakEquivalences (Complex A)).Localization ⥤
      (weakEquivalences (K ⥤ (Complex A))).Localization := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact Localization.lift (Functor.const K ⋙ (weakEquivalences (K ⥤ (Complex A))).Q)
    (constantDiagram_inverts A K) (weakEquivalences (Complex A)).Q

/-- 概要：普通の局所化圏上の実際の極限計算関手（Hovey §1.3）。
方針：元の計算関手とその擬同型保存を局所化の普遍性へ入力する。
規約：計算対象を選び直さない。
使われ方：導来 Hom 同値で特徴づける右関手。 -/
def localizedFramedLimit :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (weakEquivalences (K ⥤ (Complex A))).Localization ⥤
      (weakEquivalences (Complex A)).Localization := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact Localization.lift (framedLimitFunctor A K ⋙ (weakEquivalences (Complex A)).Q)
    (framedLimit_inverts A K) (weakEquivalences (K ⥤ (Complex A))).Q

/-- 概要：降ろした定値図式は元の定値図式と自然に比較できる（Hovey §1.3）。
方針：同じ局所化の因子化同型を使う。
規約：元の全対象と全射に自然。
使われ方：導来 Hom の同値の始域の同定。 -/
def localizedConstantDiagramComparison :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (weakEquivalences (Complex A)).Q ⋙ localizedConstantDiagram A K ≅
      Functor.const K ⋙ (weakEquivalences (K ⥤ (Complex A))).Q := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact Localization.fac _ (constantDiagram_inverts A K) _

/-- 概要：降ろした計算関手は元の計算関手と自然に比較できる（Hovey §1.3）。
方針：同じ弱同値保存による局所化の因子化同型を使う。
規約：元の図式の全対象と全射に自然。
使われ方：導来 Hom の同値の終域の同定。 -/
def localizedFramedLimitComparison :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (weakEquivalences (K ⥤ (Complex A))).Q ⋙ localizedFramedLimit A K ≅
      framedLimitFunctor A K ⋙ (weakEquivalences (Complex A)).Q := by
  let := projectiveModelCategory A
  let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
  exact Localization.fac _ (framedLimit_inverts A K) _

end SerrePositivity.EInfinity.ComplexLimits
