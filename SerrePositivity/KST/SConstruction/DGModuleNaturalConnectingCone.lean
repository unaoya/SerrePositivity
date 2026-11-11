module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInputRecovery
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeDesc

/-!
概要：元回転 square から同じ connecting cone の全厳密比較を構成する。
方針：指定零化の微分と全自然性を元 cone descent に渡す。
規約：同じ元回転比較・指定ホモトピーを保持する。
使われ方：実逆回転後の合成全比較の第一因子。
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
local notation "k" => dgModuleNaturalConeInr R D (CF) (U) (j)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "ξ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (γ) (k)

/-- 概要：同じ全自然な元回転入力の微分は指定 connecting 合成の閉元。
方針：元実 square 入力の微分式と全厳密合成の回収を使う。
規約：同じ元入力を保持。使われ方：元 cone descent の指定境界。 -/
lemma dgModuleNaturalConnectingCone_boundary (x : P) :
    (moduleHom R D ((CF).obj x) ((V).obj x)).d (-1) 0
      (dgModuleNaturalConeRotationInput R D F G η x) =
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x ≫
        dgModuleNaturalConeArrow R D (FS) (V) (ξ) x))).val := by
  rw [dgModuleNaturalConeRotationInput_recovery]
  exact (moduleConeHomotopyInput_d R D
    (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x)
    (dgModuleNaturalConeArrow R D (CF) (U) (j) x)
    (𝟙 (ForgetEnrichment.of (Complex R) ((CF).obj x)))
    (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
    (dgModuleNaturalConeRotationSquareHomotopy R D F G η x)).trans
      (congrArg (fun t => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x ≫ t))).val)
        ((congrArg (fun t => dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫ t)
          (dgModuleNaturalConeInr_arrow R D (CF) (U) (j) x).symm).trans
            (dgModuleNaturalConeArrow_comp R D (FS) (U) (V) (γ) (k) x).symm))

/-- 概要：元 connecting cone の同じ指定回転 square による全厳密比較。
方針：元実 descent を全自然な指定零化と終辺で束ねる。
規約：元二成分・全次数を保持。使われ方：実逆回転 cone の全比較。 -/
def dgModuleNaturalConnectingCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgModuleNaturalConeFunctor R D (CF) (FS) (δ)) (V) :=
  dgModuleNaturalConeDesc R D (CF) (FS) (V) (δ) (ξ)
    (dgModuleNaturalConeRotationInput R D F G η)
    (dgModuleNaturalConnectingCone_boundary R D F G η)
    (dgModuleNaturalConeRotationInput_naturality R D F G η)
end SerrePositivity.KST.SConstruction
