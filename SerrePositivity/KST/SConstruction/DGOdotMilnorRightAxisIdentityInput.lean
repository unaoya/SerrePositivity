module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInput
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisResolvedLift
public import SerrePositivity.KST.SConstruction.DGSmallPerfectFunctorImage
public import SerrePositivity.KST.SConstruction.DGHomGluingStrictSquare
public import SerrePositivity.KST.SConstruction.DGHomGluingConeFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size

/-!
概要：恒等 lax 差の対角・実 cone を、小さい厳密 dg 入力と実 S 二辺で表す。
方針：中央射と同じ逆回転基底上の Hom gluing と、元 cone の全像小模型を使う。
規約：この実 dg 入力と Sp の恒等 lax 差との全比較・列認証は後段で行う。
使われ方：LT 全長方形の右零化面の構成を厳密 dg 入力に限定して進める。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorRightAxisBase R d
local notation "I" => DGFunctor.id (C)
local notation "M" => dgHomGluingBimodule R (C) (C) (C) (I) (I)

/-- 概要：同じ小 Perf 基底の恒等二脚の実 Hom gluing。
方針：元の閉比較辺と全次数の第三 Hom 成分を使用する。
規約：小模型の対象と元の比較辺を保持する。使われ方：恒等 lax 圏の dg 候補。 -/
abbrev DGOdotMilnorRightAxisIdentityGluing :=
  DGIdentityHomGluing R (C)
local notation "L" => DGOdotMilnorRightAxisIdentityGluing R d

/-- 概要：同じ実 cone 関手の全像を保持する小さい Perf 模型。
方針：元の cone 対象族をそのまま指定追加族にする。
規約：同型な対象への選び直しはしない。使われ方：実差の dg 終域。 -/
abbrev DGOdotMilnorRightAxisIdentityDifference :=
  DGIdentityHomGluingDifference R (C)

/-- 概要：恒等二脚の同じ厳密 dg 対角。
方針：恒等四角形の strict 比較を同じ gluing 関手へ渡す。
規約：元の恒等閉比較を保つ。使われ方：右零化面の包含辺。 -/
def dgOdotMilnorRightAxisIdentityDiagonal : DGFunctor R (C) (L) :=
  dgIdentityHomGluingDiagonal R (C)

/-- 概要：同じ実 cone 関手を全像小模型へ持ち込む厳密 dg 差。
方針：元の全 Hom 作用を同じ充満小模型へ制限する。
規約：対象・写像を変更しない。使われ方：右零化面の商候補辺。 -/
def dgOdotMilnorRightAxisIdentityDifference :
    DGFunctor R (L) (DGOdotMilnorRightAxisIdentityDifference R d) :=
  dgIdentityHomGluingDifference R (C)

/-- 概要：同じ小 Perf 基底を固定 S の実頂点にする。
方針：元の全 Hom を保持する対象宇宙持ち上げ。
規約：同じ入力模型を保持する。使われ方：右零化面の左端。 -/
def dgOdotMilnorRightAxisIdentityBaseInput : PerfDGInput.{u, u + 1} R :=
  dgIdentityHomGluingBaseInput R (C)

/-- 概要：同じ恒等 Hom gluing を固定 S の実頂点にする。
方針：両小因子と閉比較辺の小ささを使用する。
規約：実 gluing 対象を保つ。使われ方：右零化面の中央。 -/
def dgOdotMilnorRightAxisIdentityGluingInput : PerfDGInput.{u, u + 1} R :=
  dgIdentityHomGluingGluingInput R (C)

/-- 概要：元の全 cone 像を保つ小模型を固定 S に置く。
方針：小さい元の像対象族の充満模型を使用する。
規約：ν 値との指定同値は後段で照合する。使われ方：右零化面の終端。 -/
def dgOdotMilnorRightAxisIdentityDifferenceInput : PerfDGInput.{u, u + 1} R :=
  dgIdentityHomGluingDifferenceInput R (C)

/-- 概要：同じ厳密対角を固定 S の実辺にする。
方針：元の dg 関手をそのまま持ち上げる。
規約：同じ閉比較を保持する。使われ方：右零化面の下辺。 -/
def dgOdotMilnorRightAxisIdentityDiagonalInputMap :
    dgOdotMilnorRightAxisIdentityBaseInput R d ⟶
      dgOdotMilnorRightAxisIdentityGluingInput R d :=
  dgIdentityHomGluingDiagonalInputMap R (C)

/-- 概要：同じ実 cone 差を固定 S の実辺にする。
方針：元の全 Hom を持つ dg 差をそのまま持ち上げる。
規約：元の差の実対象像を保つ。使われ方：右零化面の右辺。 -/
def dgOdotMilnorRightAxisIdentityDifferenceInputMap :
    dgOdotMilnorRightAxisIdentityGluingInput R d ⟶ dgOdotMilnorRightAxisIdentityDifferenceInput R d :=
  dgIdentityHomGluingDifferenceInputMap R (C)

/-- 概要：右面の中央頂点は保存済み中央射の終域と同じ入力。
方針：同じ逆回転基底上の恒等 Hom gluing を展開する。
規約：対象同値で置き換えない。使われ方：実 S 面の共有辺照合。 -/
lemma dgOdotMilnorRightAxisIdentityGluingInput_eq :
    dgOdotMilnorRightAxisIdentityGluingInput R d = dgOdotMilnorRightAxisInput R d := rfl

end SerrePositivity.KST.SConstruction
