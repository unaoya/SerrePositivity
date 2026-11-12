module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationHomInputs

/-!
概要：元実回転比較を、同じ第一・第二成分を持つ全厳密 dg 自然変換にする。
方針：元閉条件と全次数自然性を同じ元 cone lift へ適用する。
規約：元実回転成分と指定負符号を変更しない。
使われ方：実逆回転後の合成比較を作る全回転比較因子。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)

/-- 概要：同じ元回転比較の全厳密 dg 自然変換。
方針：元二成分の閉性と全自然性を既存の同じ cone lift へ渡す。
規約：追加の存在入力を加えない。
使われ方：同じ実 connecting cone 比較の全自然性を構成する第一因子。 -/
def dgModuleNaturalConeRotationHom : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (FS) (U) :=
  dgModuleNaturalConeLift R D G (CF) (FS) (ν)
    (fun x => moduleConeRotationFirst R D (a x))
    (fun x => moduleConeRotationSecond R D (a x))
    (fun x => moduleConeRotationFirst_closed R D (a x))
    (dgModuleNaturalConeRotationHom_boundary R D F G η)
    (dgModuleNaturalConeRotationFirst_naturality R D F G η)
    (dgModuleNaturalConeRotationSecond_naturality R D F G η)
end SerrePositivity.KST.SConstruction
