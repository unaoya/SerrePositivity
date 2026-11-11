module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeComonad

/-!
# 自由相対圏の解像の全次数・augmentation・外側作用素

概要：Dwyer–Kan の自由解像の各次数を同じ自由相対圏の反復で構成する。
方針：comonad の余単位と対角から augmentation と外側作用素を作る。
規約：全単体作用素と単体的局所化は後続で構成する。
使われ方：CAlg_R の自由単体的解像の次数ごとの入力。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

open CategoryTheory

/-- 概要：同じ自由相対圏関手の n 回反復（Dwyer–Kan）。
方針：恒等関手から同じ自由関手を逐次合成する。
規約：全次数で元の指定矢の列を保持する。
使われ方：自由解像の次数と外側の作用素。 -/
def freePower : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}
  | 0 => 𝟭 _
  | n + 1 => freePower n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor

/-- 概要：反復自由相対圏から元の相対圏への自然な合成（Dwyer–Kan）。
方針：外側の列を合成してから前の次数の augmentation を適用する。
規約：元の相対圏に関して自然な同じ相対関手。
使われ方：自由解像から元の係数圏への augmentation。 -/
def freePowerAugmentation : (n : ℕ) → freePower.{u} n ⟶ 𝟭 _
  | 0 => 𝟙 _
  | n + 1 => Functor.whiskerLeft (freePower n) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit ≫
      (Functor.rightUnitor (freePower n)).hom ≫ freePowerAugmentation n

/-- 概要：自由解像の n 次は自由相対圏の n+1 回反復（Dwyer–Kan）。
方針：同じ反復関手の次数を一つ上げる。
規約：零次も実際の自由圏。
使われ方：単体的局所化の次数ごとの圏。 -/
abbrev freeResolutionLevel (n : ℕ) := freePower.{u} (n + 1)

/-- 概要：自由解像の各次数から元の相対圏への augmentation（Dwyer–Kan）。
方針：同じ反復自由関手の自然な合成を使う。
規約：すべての相対係数関手に自然。
使われ方：元の E 代数の射の追跡。 -/
abbrev freeResolutionAugmentation (n : ℕ) : freeResolutionLevel.{u} n ⟶ 𝟭 _ :=
  freePowerAugmentation (n + 1)

/-- 概要：自由解像の外側の面は最外層の列の合成（Dwyer–Kan）。
方針：前の次数の後ろへ同じ余単位を適用する。
規約：全次数に定義した同じ自然変換。
使われ方：単体作用素と augmentation の比較。 -/
def freeResolutionOuterFace (n : ℕ) :
    freeResolutionLevel.{u} (n + 1) ⟶ freeResolutionLevel n :=
  Functor.whiskerLeft (freePower (n + 1)) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit ≫
    (Functor.rightUnitor (freePower (n + 1))).hom

/-- 概要：自由解像の外側の退化は最外層の矢を一文字の列にする（Dwyer–Kan）。
方針：同じ対角を反復自由関手の後ろへ適用する。
規約：各次数の実際の自由圏の関手。
使われ方：単体的自由解像の退化作用素の出発点。 -/
def freeResolutionOuterDegeneracy (n : ℕ) :
    freeResolutionLevel.{u} n ⟶ freeResolutionLevel (n + 1) :=
  Functor.whiskerLeft (freePower n) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeDiagonal ≫
    (Functor.associator (freePower n) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor).inv

/-- 概要：外側の面は元の augmentation と厳密に両立（Dwyer–Kan）。
方針：反復自由関手の augmentation の再帰式を評価する。
規約：同じ自然変換の等式。
使われ方：元の射の次数間の追跡。 -/
lemma freeResolutionOuterFace_augmentation (n : ℕ) :
    freeResolutionOuterFace.{u} n ≫ freeResolutionAugmentation n =
      freeResolutionAugmentation (n + 1) := rfl

/-- 概要：外側の退化の後の外側の面は恒等（Dwyer–Kan）。
方針：同じ comonad の左余単位則を各反復対象で評価する。
規約：全次数で実際の相対関手の厳密な等式。
使われ方：自由解像の面退化恒等式の出発点。 -/
lemma freeResolutionOuterDegeneracy_face (n : ℕ) :
    freeResolutionOuterDegeneracy.{u} n ≫ freeResolutionOuterFace n =
      𝟙 (freeResolutionLevel n) := by
  apply NatTrans.ext
  funext C
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeDiagonal.app ((freePower n).obj C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor.obj ((freePower n).obj C)) = 𝟙 _ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad.left_counit ((freePower n).obj C)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeDiagonal.app ((freePower n).obj C) ≫ 𝟙 _) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor.obj ((freePower n).obj C)) ≫ 𝟙 _) = 𝟙 _
  simpa only [Category.comp_id] using h


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
