module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingNullSquare
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisIdentityInput
public import SerrePositivity.KST.SConstruction.DGHomGluingTargetContraction
public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullSquare

/-!
概要：恒等 Hom gluing の同じ対角・実 cone 差から、固定 S の実零化面を構成する。
方針：恒等閉比較の実 cone の指定収縮を、全像小模型と宇宙持ち上げで保持する。
規約：対象別収縮を使う商延長であり、自然な収縮や Verdier 認証は仮定しない。
使われ方：LT 全長方形の右面と、その固定 ν 像の全境界比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorRightAxisBase R d
local notation "I" => DGFunctor.id (C)
local notation "L" => DGOdotMilnorRightAxisIdentityGluing R d
local notation "D" => DGOdotMilnorRightAxisIdentityDifference R d

/-- 概要：同じ strict 対角の実閉比較は恒等そのもの。
方針：比較対象の閉射回収を元の恒等四角形に特殊化する。
規約：同型類でなく閉射の等号。使われ方：同じ実 cone の収縮。 -/
abbrev dgOdotMilnorRightAxisIdentityDiagonal_targetMap :=
  dgIdentityHomGluingDiagonal_targetMap R (C)

/-- 概要：同じ対角像の実 cone における指定次数 −1 元。
方針：恒等比較の既存収縮を同じ全像小模型で使用する。
規約：像対象を選び直さない。使われ方：全対象商の延長データ。 -/
abbrev dgOdotMilnorRightAxisIdentityContractingElement :=
  dgIdentityHomGluingContractingElement R (C)

/-- 概要：同じ小模型内の指定収縮元の微分は同じ像の恒等元。
方針：全 Hom を保持する包含の定義から既存の微分式を使用する。
規約：同じ実 cone の式。使われ方：固定 S の指定収縮付き合成。 -/
abbrev dgOdotMilnorRightAxisIdentityContractingElement_d :=
  dgIdentityHomGluingContractingElement_d R (C)

/-- 概要：同じ固定 S の対角・差の合成に指定収縮を与える。
方針：対象宇宙を持ち上げても元の全 Hom と微分を使用する。
規約：自然な収縮を仮定しない。使われ方：Sp 正本の実零化面構成。 -/
abbrev dgOdotMilnorRightAxisIdentityContracted :=
  dgIdentityHomGluingContracted R (C)

/-- 概要：恒等 Hom gluing の元の四辺を持つ固定 S の実零化面。
方針：指定収縮の同じ全対象商延長を使用する。
規約：ν 像の列認証は別に行う。使われ方：LT 長方形の右面。 -/
abbrev dgOdotMilnorRightAxisIdentityNullSquare :=
  dgIdentityHomGluingNullSquare R (C)

/-- 概要：同じ実零化面の四辺は元の対角・差・商包含・商延長。
方針：同じ選択された面の境界を回収する。
規約：全一単体の等号を保持する。使われ方：指定全境界での貼合せ。 -/
abbrev dgOdotMilnorRightAxisIdentityNullSquare_edges :=
  dgIdentityHomGluingNullSquare_edges R (C)

end SerrePositivity.KST.SConstruction
