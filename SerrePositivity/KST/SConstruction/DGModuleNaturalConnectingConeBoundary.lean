module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeComposite

/-!
概要：元 connecting cone の合成全比較が指定包含辺を回収することを示す。
方針：元 descent と二回目の回転逆の包含回収を順に使う。
規約：同じ全比較の成分についての厳密等式。
使われ方：元実上二単体の指定境界の照合。
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
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "ξ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (γ) (k)
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "θ" => dgModuleNaturalConnectingCone R D F G η
local notation "ρ" => dgModuleNaturalConeRotationInv R D G (CF) (ν)
local notation "δν" => dgModuleNaturalConeConnecting R D G (CF) (ν)

/-- 概要：同じ二回目の回転逆は同じ右包含の後で元 connecting を回収。
方針：同じ元 descent の包含等式を適用する。
規約：実閉射の厳密等式。使われ方：合成比較の指定包含辺。 -/
lemma dgModuleNaturalConnectingConeRotationInv_inr (x : P) :
    dgModuleNaturalConeArrow R D (U) (V) (k) x ≫
      dgModuleNaturalConeArrow R D (V) (GS) (ρ) x =
        dgModuleNaturalConeArrow R D (U) (GS) (δν) x :=
  (congrArg (fun t => t ≫ dgModuleNaturalConeArrow R D (V) (GS) (ρ) x)
    (dgModuleNaturalConeInr_arrow R D (CF) (U) (j) x)).trans
      (dgModuleNaturalConeDesc_inr R D (CF) (U) (GS) (j) (δν)
        (fun _ => 0) (dgModuleNaturalConeRotationInv_boundary R D G (CF) (ν))
        (by intro x y n z; simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, smul_zero]) x)

/-- 概要：同じ全 connecting cone 比較の包含制限は元全回転比較と connecting の合成。
方針：元 descent の終辺回収と二回目の元包含回収を合成する。
規約：元実比較を保持。使われ方：指定上二単体の元包含境界。 -/
lemma dgModuleNaturalConnectingConeComposite_inr (x : P) :
    moduleConeInr R D (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x) ≫
      dgModuleNaturalConeArrow R D (CD) (GS)
        (dgModuleNaturalConnectingConeComposite R D F G η) x =
    dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫
      dgModuleNaturalConeArrow R D (U) (GS) (δν) x := by
  rw [dgModuleNaturalConnectingConeComposite_arrow]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ dgModuleNaturalConeArrow R D (V) (GS) (ρ) x)
      (dgModuleNaturalConeDesc_inr R D (CF) (FS) (V) (δ) (ξ)
        (dgModuleNaturalConeRotationInput R D F G η)
        (dgModuleNaturalConnectingCone_boundary R D F G η)
        (dgModuleNaturalConeRotationInput_naturality R D F G η) x)).trans
      ((congrArg (fun t => t ≫ dgModuleNaturalConeArrow R D (V) (GS) (ρ) x)
        (dgModuleNaturalConeArrow_comp R D (FS) (U) (V) (γ) (k) x)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun t => dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫ t)
            (dgModuleNaturalConnectingConeRotationInv_inr R D F G η x)))))
end SerrePositivity.KST.SConstruction
