module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraLocalization
public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizedFreeResolution
public import Mathlib.CategoryTheory.Category.ULift

/-!
# E 代数を Dwyer–Kan 自由解像へ渡す具体的な相対圏

概要：任意の可換環上の cofibrant E 代数を自由相対圏の comonad へ渡す。
方針：Hom の宇宙だけを揃え、元の包含・置換・弱同値を保持する。
規約：対象は元の cofibrant 代数、Hom は ULift による同じ代数射。
使われ方：CAlg_R の自由単体的解像の始域と忘却関手の入力。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization

variable (A : Type u) [CommRing A]

/-- 概要：cofibrant E 代数の相対圏を DK 解像の同じ宇宙へ束ねる（Dwyer–Kan）。
方針：元の full subcategory の Hom を ULift し、同じ弱同値類を引き戻す。
規約：対象の宇宙 u+1 に Hom を揃え、基礎環や元の代数を変更しない。
使われ方：自由相対圏 comonad の具体的な入力。 -/
def cofibrantAlgebraRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} where
  category := Cat.of (ULiftHom.{u + 1} (CofibrantAlgebra A))
  weakEquivalences := (cofibrantAlgebraWeakEquivalences A).inverseImage (ULiftHom.down.{u, u + 1,
    u + 1} (C := CofibrantAlgebra A))
  isMultiplicative := inferInstance

/-- 概要：DK 入力から元の E 代数圏への同じ包含（Dwyer–Kan）。
方針：ULift の Hom を戻して元の包含を合成する。
規約：元の対象と代数射を保持する。
使われ方：相対圏の単体的局所化と元の E 代数モデルの比較。 -/
def cofibrantAlgebraDKInclusion :
    (cofibrantAlgebraRelativeCategory A).category ⥤ (operad A).Algebra :=
  (ULiftHom.down.{u, u + 1, u + 1} (C := CofibrantAlgebra A)) ⋙ cofibrantAlgebraInclusion A

/-- 概要：DK 入力の指定矢は元の複体射の擬同型（Dwyer–Kan）。
方針：Hom の ULift と包含に沿う逆像の定義を展開する。
規約：基礎環と元の複体射を保持する。
使われ方：具体的な忘却・置換の相対性の判定。 -/
lemma cofibrantAlgebraRelativeCategory_weakEquivalences_iff
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences f ↔
      QuasiIso ((cofibrantAlgebraDKInclusion A).map f).hom := Iff.rfl

/-- 概要：DK 入力の包含は元の弱同値を保つ相対関手（Dwyer–Kan）。
方針：同じ擬同型の判定を使う。
規約：実際の E 代数モデルを局所的に選ぶ。
使われ方：単体的局所化に沿う包含の関手化。 -/
def cofibrantAlgebraDKInclusionRelative :
    let := modelCategory A
    LocalizerMorphism (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (weakEquivalences (operad A).Algebra) := by
  let := modelCategory A
  exact ⟨cofibrantAlgebraDKInclusion A, fun _ _ _ hf => hf⟩

/-- 概要：元の全代数の関手的置換を同じ DK 入力へ送る（Hovey §1.2）。
方針：既存の cofibrant 置換の Hom を ULift する。
規約：元の置換の対象・射を変更しない。
使われ方：単体的局所化の具体的な対象の供給。 -/
def cofibrantAlgebraDKReplacement :
    (operad A).Algebra ⥤ (cofibrantAlgebraRelativeCategory A).category :=
  cofibrantAlgebraReplacement A ⋙ (ULiftHom.up.{u, u + 1, u + 1} (C := CofibrantAlgebra A))

/-- 概要：DK 入力への置換を包含で戻すと元の置換に厳密に一致（Hovey §1.2）。
方針：ULift の順逆の定義を評価する。
規約：新たな対象の選択や自然同型を使わない。
使われ方：元の Map^h の同じ置換と DK 入力との接続。 -/
lemma cofibrantAlgebraDKReplacement_comp_inclusion :
    cofibrantAlgebraDKReplacement A ⋙ cofibrantAlgebraDKInclusion A =
      framedLimitProbeFunctor A := rfl

/-- 概要：DK 入力への置換は元の弱同値を保つ（Dwyer–Kan）。
方針：同じ具体的な cofibrant 置換の擬同型保存を使う。
規約：元の代数に cofibrancy は要求しない。
使われ方：元の全代数相対圏から単体的局所化への関手化。 -/
def cofibrantAlgebraDKReplacementRelative :
    let := modelCategory A
    LocalizerMorphism (weakEquivalences (operad A).Algebra)
      (cofibrantAlgebraRelativeCategory A).weakEquivalences := by
  let := modelCategory A
  exact ⟨cofibrantAlgebraDKReplacement A,
    fun _ _ f hf => framedLimitProbeFunctor_map_quasiIso A f hf⟩

/-- 概要：DK 入力から元の複体へ忘却する関手（BM 命題 4.1）。
方針：同じ包含と元の忘却を合成する。
規約：cofibrant E 代数の底の cofibrancy は要求しない。
使われ方：U の単体的局所化による関手化の入力。 -/
def cofibrantAlgebraDKForget :
    (cofibrantAlgebraRelativeCategory A).category ⥤ Complex A :=
  cofibrantAlgebraDKInclusion A ⋙ Operad.Algebra.forget (operad A)

/-- 概要：DK 入力の忘却は複体の擬同型を保つ相対関手（BM 命題 4.1）。
方針：元の指定矢の同じ底の擬同型を使う。
規約：忘却先は全複体の相対圏で、底の cofibrancy 条件は加えない。
使われ方：CAlg_R から D(R) への関手の構成。 -/
def cofibrantAlgebraDKForgetRelative :
    LocalizerMorphism (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)) :=
  ⟨cofibrantAlgebraDKForget A, fun _ _ _ hf => hf⟩

/-- 概要：DK 自由解像の n 次へ実際の E 代数相対圏を代入（Dwyer–Kan）。
方針：元の cofibrant 代数の相対圏へ反復自由関手を適用する。
規約：全次数で元の弱同値だけからなる列の条件を保持する。
使われ方：単体的局所化の次数ごとの圏の具体的な入力。 -/
abbrev cofibrantAlgebraFreeLevel (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeResolutionLevel n).obj (cofibrantAlgebraRelativeCategory A)

/-- 概要：各自由次数から元の DK 入力への同じ augmentation（Dwyer–Kan）。
方針：元の反復自由解像の自然変換を具体的な相対圏で評価する。
規約：元の代数射の列を逐次合成する。
使われ方：単体的局所化と元の代数射の比較。 -/
abbrev cofibrantAlgebraFreeAugmentation (n : ℕ) :
    cofibrantAlgebraFreeLevel A n ⟶ cofibrantAlgebraRelativeCategory A :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeResolutionAugmentation n).app (cofibrantAlgebraRelativeCategory A)

/-- 概要：元の cofibrant E 代数相対圏の全自由単体的解像（Dwyer–Kan）。
方針：同じ相対圏を汎用自由解像へ代入する。
規約：通常の単体圏上の全作用素を保持する。
使われ方：CAlg_R の次数ごとの単体的局所化の入力。 -/
def cofibrantAlgebraFreeResolution :
    SimplicialObject _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} :=
  freeResolution (cofibrantAlgebraRelativeCategory A)

/-- 概要：全自由解像から元の E 代数相対圏への augmentation（Dwyer–Kan）。
方針：元の汎用自由解像の同じ自然変換を使う。
規約：全単体作用素と指定する矢の類を保持する。
使われ方：元の E 代数射と単体的局所化の比較。 -/
def cofibrantAlgebraFreeResolutionAugmentation :
    cofibrantAlgebraFreeResolution A ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (cofibrantAlgebraRelativeCategory A) :=
  freeResolutionAugmentationNatTrans (cofibrantAlgebraRelativeCategory A)

/-- 概要：全自由次数を厳密に局所化した E 代数の単体的図式（Dwyer–Kan）。
方針：具体的な cofibrant 相対圏を同じ次数ごとの局所化へ代入する。
規約：各次数の指定矢は元の擬同型だけからなる列。
使われ方：固定対象を持つ DK 単体的圏の構成。 -/
def cofibrantAlgebraLocalizedFreeResolution : SimplicialObject Cat.{u + 1, u + 1} :=
  localizedFreeResolution (cofibrantAlgebraRelativeCategory A)

/-- 概要：次数ごとの局所化から元の普通の局所化への augmentation（Dwyer–Kan）。
方針：元の同じ全単体的 augmentation を具体的な E 代数相対圏で評価する。
規約：全単体作用素と元の擬同型の反転を保持する。
使われ方：DK 写像空間と元の局所化 Hom の比較。 -/
def cofibrantAlgebraLocalizedFreeResolutionAugmentation :
    cofibrantAlgebraLocalizedFreeResolution A ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj
        (Cat.of (cofibrantAlgebraRelativeCategory A).weakEquivalences.Localization) :=
  localizedFreeResolutionAugmentation (cofibrantAlgebraRelativeCategory A)

end SerrePositivity.EInfinity.BarrattEccles
