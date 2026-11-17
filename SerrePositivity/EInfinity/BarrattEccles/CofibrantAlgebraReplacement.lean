module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebras
public import SerrePositivity.EInfinity.BarrattEccles.FramedLimitProbeFunctor

/-!
# Cofibrant E 代数への元の関手的置換

概要：Dwyer–Kan の相対圏比較に同じ具体的な cofibrant 置換を使う。
方針：既存の試験始域関手を full subcategory へ持ち上げる。
規約：元の代数の cofibrancy は仮定せず、元の置換と比較射を保持する。
使われ方：cofibrant 相対圏と全 E 代数相対圏の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory _root_.HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：全 E 代数から cofibrant E 代数への関手的置換（Hovey §1.2）。
方針：元の試験始域関手をその cofibrancy により full subcategory へ持ち上げる。
規約：対象と射は元の関手的分解そのもの。
使われ方：cofibrant 相対圏を使う単体的局所化の対象の置換。 -/
def cofibrantAlgebraReplacement : (operad A).Algebra ⥤ CofibrantAlgebra A := by
  let := modelCategory A
  exact (cofibrantObjects (operad A).Algebra).lift (framedLimitProbeFunctor A)
    (framedLimitProbe_cofibrant A)

/-- 概要：置換の包含像は元の試験始域関手と厳密に一致（Hovey §1.2）。
方針：full subcategory への lift の定義を評価する。
規約：新しい置換対象や比較同型を選ばない。
使われ方：既存の Map^h と単体的局所化の同じ置換の照合。 -/
lemma cofibrantAlgebraReplacement_comp_inclusion :
    cofibrantAlgebraReplacement A ⋙ cofibrantAlgebraInclusion A = framedLimitProbeFunctor A :=
  rfl

/-- 概要：置換は元の擬同型を保つ相対関手（Dwyer–Kan）。
方針：元の試験始域関手の擬同型保存を使う。
規約：元の具体的なモデル構造を局所的に選ぶ。
使われ方：相対圏の局所化へ降ろす逆向きの関手。 -/
def cofibrantAlgebraReplacementRelative :
    let := modelCategory A
    LocalizerMorphism (weakEquivalences (operad A).Algebra)
      (cofibrantAlgebraWeakEquivalences A) := by
  let := modelCategory A
  exact ⟨cofibrantAlgebraReplacement A,
    fun _ _ f hf => framedLimitProbeFunctor_map_quasiIso A f hf⟩

/-- 概要：包含後の置換から元の全代数への自然な擬同型（Hovey §1.2）。
方針：既存の試験始域比較の同じ自然変換を使う。
規約：元の全代数とすべての代数射に自然。
使われ方：相対圏の比較の一方のホモトピー逆。 -/
def cofibrantAlgebraReplacementComparison :
    cofibrantAlgebraReplacement A ⋙ cofibrantAlgebraInclusion A ⟶ 𝟭 (operad A).Algebra :=
  framedLimitProbeComparisonNatTrans A

/-- 概要：置換比較の全成分は元の弱同値（Hovey §1.2）。
方針：元の試験始域比較の擬同型性を使う。
規約：元の代数に cofibrancy は要求しない。
使われ方：元の全代数圏の局所化での比較の反転。 -/
lemma cofibrantAlgebraReplacementComparison_weakEquivalence (X : (operad A).Algebra) :
    let := modelCategory A
    weakEquivalences (operad A).Algebra
      ((cofibrantAlgebraReplacementComparison A).app X) :=
  framedLimitProbeComparison_quasiIso A X

/-- 概要：cofibrant 対象に制限した同じ置換の比較（Hovey §1.2）。
方針：元の比較射を full subcategory の射として束ねる。
規約：元の包含と同じ置換を使う。
使われ方：相対圏の比較のもう一方のホモトピー逆。 -/
def cofibrantAlgebraRestrictedComparison :
    cofibrantAlgebraInclusion A ⋙ cofibrantAlgebraReplacement A ⟶ 𝟭 (CofibrantAlgebra A) where
  app X := ObjectProperty.homMk (framedLimitProbeComparison A X.obj)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (framedLimitProbeComparisonNatTrans A).naturality f.hom

/-- 概要：制限した置換比較の全成分は同じ相対弱同値（Dwyer–Kan）。
方針：full subcategory の射の底の擬同型性を使う。
規約：元の cofibrant 代数の全射を保つ。
使われ方：cofibrant 相対圏の局所化での比較の反転。 -/
lemma cofibrantAlgebraRestrictedComparison_weakEquivalence (X : CofibrantAlgebra A) :
    cofibrantAlgebraWeakEquivalences A
      ((cofibrantAlgebraRestrictedComparison A).app X) :=
  framedLimitProbeComparison_quasiIso A X.obj

end SerrePositivity.EInfinity.BarrattEccles
