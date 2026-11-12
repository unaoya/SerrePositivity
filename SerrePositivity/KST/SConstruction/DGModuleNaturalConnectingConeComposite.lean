module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeNative

/-!
概要：元 connecting cone の全比較に同じ二回目の回転逆を合成する。
方針：既存の全厳密比較の合成を使い、同じ閉成分の合成を回収する。
規約：元の指定ホモトピーと回転逆を保持する。
使われ方：実逆回転後の合成全比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "j" => dgModuleNaturalConeInr R D G (CF) (ν)
local notation "V" => dgModuleNaturalConeFunctor R D (CF) (U) (j)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "θ" => dgModuleNaturalConnectingCone R D F G η
local notation "ρ" => dgModuleNaturalConeRotationInv R D G (CF) (ν)

/-- 概要：元 connecting cone から元終域の shift への全厳密合成比較。
方針：同じ指定 square の全比較と二回目の元回転逆を合成する。
規約：実回転成分を変更しない。使われ方：実逆回転後の全比較の合成部分。 -/
def dgModuleNaturalConnectingConeComposite : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (CD) (GS) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (θ) (ρ)

/-- 概要：元合成全比較の閉成分は元二比較の同じ合成。
方針：既存の全厳密合成回収を適用する。
規約：元実成分を保持。使われ方：指定包含と元実 cone 射の回収。 -/
lemma dgModuleNaturalConnectingConeComposite_arrow (x : P) :
    dgModuleNaturalConeArrow R D (CD) (GS)
      (dgModuleNaturalConnectingConeComposite R D F G η) x =
    dgModuleNaturalConeArrow R D (CD) (V) (θ) x ≫
      dgModuleNaturalConeArrow R D (V) (GS) (ρ) x :=
  dgModuleNaturalConeArrow_comp R D (CD) (V) (GS) (θ) (ρ) x

/-- 概要：同じ全合成比較の各閉成分は K(D) の同値。
方針：元二比較の同値を元閉成分合成へ適用する。
規約：指定元成分を保持。使われ方：native 全合成比較の可逆性。 -/
lemma dgModuleNaturalConnectingConeComposite_isIso (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (CD) (GS)
        (dgModuleNaturalConnectingConeComposite R D F G η) x)) := by
  rw [dgModuleNaturalConnectingConeComposite_arrow, CategoryTheory.Functor.map_comp]
  haveI := dgModuleNaturalConnectingCone_isIso R D F G η x
  haveI := dgModuleNaturalConeRotationInv_isIso R D G (CF) (ν) x
  infer_instance
end SerrePositivity.KST.SConstruction
