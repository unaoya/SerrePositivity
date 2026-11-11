module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeBoundary

/-!
概要：元全 connecting cone 比較の包含制限の指定負符号を回収する。
方針：同じ元回転 lift と connecting の実射回収を元回転恒等式へ代入する。
規約：元射の shift と元負符号を保持する。
使われ方：実逆回転後の上二単体の指定境界。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma rotationSign {M N : ModuleCategory R D} (f : M ⟶ N)
    (ψ : N ⟶ moduleCone R D f) (hψ : ψ = moduleConeInr R D f)
    (hb : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
      (ForgetEnrichment.to (Complex R) (moduleCone R D f))).d 0 1 (moduleConeRotationSecond R D f) +
      (show (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
        (ForgetEnrichment.to (Complex R) (moduleCone R D f))).X 1 from
        (eHomWhiskerLeft (Complex R) (moduleShiftObj R D 1 M) ψ).f 1
          (moduleConeRotationFirst R D f)) = 0)
    (r : moduleShiftObj R D 1 M ⟶ moduleCone R D ψ)
    (d : moduleCone R D ψ ⟶ moduleShiftObj R D 1 N)
    (er : r = moduleConeLiftOfCycle R D ψ (moduleConeRotationFirst R D f)
      (moduleConeRotationSecond R D f) (moduleConeRotationFirst_closed R D f) hb)
    (ed : d = moduleConeConnecting R D ψ) : r ≫ d = -f⟦(1 : ℤ)⟧' := by
  cases er
  cases ed
  cases hψ
  exact moduleConeRotation_connecting R D f
variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "δν" => dgModuleNaturalConeConnecting R D G (CF) (ν)
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)

/-- 概要：同じ全回転比較と次の connecting の合成は元射 shift の負。
方針：元実 lift と connecting の成分を元回転恒等式に戻す。
規約：指定負符号を保持。使われ方：元全比較の指定包含制限。 -/
lemma dgModuleNaturalConeRotationHom_connecting (x : P) :
    dgModuleNaturalConeArrow R D (FS) (U) (γ) x ≫
      dgModuleNaturalConeArrow R D (U) (GS) (δν) x = -(a x)⟦(1 : ℤ)⟧' :=
  rotationSign R D (a x) (dgModuleNaturalConeArrow R D G (CF) (ν) x)
    (dgModuleNaturalConeInr_arrow R D F G η x)
    (dgModuleNaturalConeRotationHom_boundary R D F G η x)
    (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
    (dgModuleNaturalConeArrow R D (U) (GS) (δν) x)
    (dgModuleNaturalConeRotationHom_arrow R D F G η x)
    (dgModuleNaturalConeConnecting_arrow R D G (CF) (ν) x)

/-- 概要：元全 connecting cone 合成比較は包含後で元射 shift の負を回収する。
方針：元包含境界と同じ全回転の符号等式を合成する。
規約：同じ元実射の厳密等式。使われ方：実上二単体の指定境界。 -/
lemma dgModuleNaturalConnectingConeComposite_inr_sign (x : P) :
    moduleConeInr R D (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x) ≫
      dgModuleNaturalConeArrow R D (CD) (GS)
        (dgModuleNaturalConnectingConeComposite R D F G η) x = -(a x)⟦(1 : ℤ)⟧' :=
  (dgModuleNaturalConnectingConeComposite_inr R D F G η x).trans
    (dgModuleNaturalConeRotationHom_connecting R D F G η x)
end SerrePositivity.KST.SConstruction
