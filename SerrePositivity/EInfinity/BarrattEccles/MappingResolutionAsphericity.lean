module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpace
public import SerrePositivity.EInfinity.FrameHom.ResolutionAsphericity

/-!
# 実際の E 代数の写像空間に使う分解の asphericity

概要：任意の可換環上の元の Map^h の分解を Low 命題 3.6 の可縮性へ代入する。
方針：同じ転送モデルと同じ関手的分解を局所的に選ぶ。
規約：元の代数に cofibrancy を要求せず、単体集合モデルを入力しない。
使われ方：特殊な三本矢への右射の具体的な分解側の余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.Reedy

variable (A : Type u) [CommRing A]

/-- 概要：元の E 代数への自明 fibration の全 slice（Low 命題 3.6）。
方針：実際の転送モデルの自明 fibration を使う。
規約：元の代数と全可換三角形を保持する。
使われ方：元の写像空間の分解の asphericity の値圏。 -/
abbrev algebraTrivialFibrationOver (X : (operad A).Algebra) :=
  let := modelCategory A
  FrameHom.TrivialFibrationOver X

/-- 概要：同じ Map^h の分解は元の自明 fibration の slice への関手（Low 命題 3.6）。
方針：元の mappingCofibrantFactorization の全作用素を代入する。
規約：元の分解と augmentation を変更しない。
使われ方：実際の右比較の分解側の全 comma 圏。 -/
def mappingResolutionOverFunctor (X : (operad A).Algebra) :
    SimplexCategory ⥤ algebraTrivialFibrationOver A X := by
  let := modelCategory A
  exact FrameHom.resolutionOverFunctor
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X)

/-- 概要：元の分解の全 comma 圏の終射は anodyne 反転後に可逆（Low 命題 3.6）。
方針：元の分解の Reedy cofibrancy と同じ持ち上げ空間の収縮を適用する。
規約：任意の可換環・任意の代数への全自明 fibration を扱う。
使われ方：三本矢への右射の具体的な asphericity の入力。 -/
lemma mappingResolutionCommaTerminal_localized_isIso (X : (operad A).Algebra)
    (t : algebraTrivialFibrationOver A X) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (SSet.stdSimplex.isTerminalObj₀.from
        (nerve (CostructuredArrow (mappingResolutionOverFunctor A X) t)))) := by
  let := modelCategory A
  exact FrameHom.resolutionCommaTerminal_image_isIso
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X) t
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions)

end SerrePositivity.EInfinity.BarrattEccles
