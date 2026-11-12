module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationHomComparison
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationPrimitive

/-!
概要：元全回転比較の指定回転ホモトピーの同じ微分境界を実証する。
方針：元右包含の回収を同じ元加群回転境界に代入する。
規約：元次数 −1 元・元 connecting・元回転比較を保持する。
使われ方：同じ connecting cone 射を全関手族へ束ねる指定 square。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元包含と厳密に等しい指定包含を用いた回転 lift の指定微分境界。
方針：元包含の等号を消去して従来の同じ回転ホモトピー境界を使う。
規約：元実 lift と元斉次元を保持。使われ方：全族の各成分の境界回収。 -/
lemma dgModuleRotationLift_boundary {M N : ModuleCategory R D} (f : M ⟶ N)
    (ψ : N ⟶ moduleCone R D f) (hψ : ψ = moduleConeInr R D f)
    (hb : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
      (ForgetEnrichment.to (Complex R) (moduleCone R D f))).d 0 1 (moduleConeRotationSecond R D f) +
      (show (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
        (ForgetEnrichment.to (Complex R) (moduleCone R D f))).X 1 from
        (eHomWhiskerLeft (Complex R) (moduleShiftObj R D 1 M) ψ).f 1
          (moduleConeRotationFirst R D f)) = 0) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (ForgetEnrichment.to (Complex R) (moduleCone R D ψ))).d (-1) 0
      (-compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
        (y := ForgetEnrichment.to (Complex R) N)
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D ψ))
        (moduleConeInlElement R D ψ) (moduleConeSndElement R D f) (zero_add (-1))) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (moduleConeConnecting R D f ≫ moduleConeLiftOfCycle R D ψ
          (moduleConeRotationFirst R D f) (moduleConeRotationSecond R D f)
          (moduleConeRotationFirst_closed R D f) hb))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (moduleConeInr R D ψ))).val := by
  cases hψ
  exact moduleConeRotationConnectingElement_d R D f

private lemma rotationBoundaryOfRecovery {M N : ModuleCategory R D} (f : M ⟶ N)
    (ψ : N ⟶ moduleCone R D f) (hψ : ψ = moduleConeInr R D f)
    (hb : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
      (ForgetEnrichment.to (Complex R) (moduleCone R D f))).d 0 1 (moduleConeRotationSecond R D f) +
      (show (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleShiftObj R D 1 M))
        (ForgetEnrichment.to (Complex R) (moduleCone R D f))).X 1 from
        (eHomWhiskerLeft (Complex R) (moduleShiftObj R D 1 M) ψ).f 1
          (moduleConeRotationFirst R D f)) = 0)
    (d : moduleCone R D f ⟶ moduleShiftObj R D 1 M)
    (r : moduleShiftObj R D 1 M ⟶ moduleCone R D ψ)
    (j : moduleCone R D f ⟶ moduleCone R D ψ)
    (ed : d = moduleConeConnecting R D f)
    (er : r = moduleConeLiftOfCycle R D ψ (moduleConeRotationFirst R D f)
      (moduleConeRotationSecond R D f) (moduleConeRotationFirst_closed R D f) hb)
    (ej : j = moduleConeInr R D ψ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (ForgetEnrichment.to (Complex R) (moduleCone R D ψ))).d (-1) 0
      (-compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
        (y := ForgetEnrichment.to (Complex R) N)
        (z := ForgetEnrichment.to (Complex R) (moduleCone R D ψ))
        (moduleConeInlElement R D ψ) (moduleConeSndElement R D f) (zero_add (-1))) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (d ≫ r))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) j)).val := by
  cases ed
  cases er
  cases ej
  exact dgModuleRotationLift_boundary R D f ψ hψ hb

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "j" => dgModuleNaturalConeInr R D G (CF) (ν)

/-- 概要：元全回転ホモトピーの微分は同じ connecting・全回転比較と二重包含の差。
方針：元実 lift の閉射回収と同じ元包含の回収を指定境界へ代入する。
規約：元全次数自然性を持つ指定元を保持。
使われ方：実 connecting cone 比較の全 square の同じ微分境界。 -/
lemma dgModuleNaturalConeRotationSquare_boundary (x : P) :
    (moduleHom R D ((CF).obj x) ((U).obj x)).d (-1) 0
      (dgModuleNaturalConeRotationHomotopyElement R D F G η x) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x ≫
          dgModuleNaturalConeArrow R D (FS) (U) (γ) x))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgModuleNaturalConeArrow R D (CF) (U) (j) x))).val := by
  dsimp only [dgModuleNaturalConeRotationHomotopyElement,
    dgModuleNaturalConeRotationPrimitive, dgModuleNaturalConeNullHomotopyElement,
    dgModuleNaturalConeRetractionElement]
  exact rotationBoundaryOfRecovery R D
    (M := ForgetEnrichment.of (Complex R) (F.obj x))
    (N := ForgetEnrichment.of (Complex R) (G.obj x))
    (a x) (dgModuleNaturalConeArrow R D G (CF) (ν) x)
    (dgModuleNaturalConeInr_arrow R D F G η x)
    (dgModuleNaturalConeRotationHom_boundary R D F G η x)
    (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x)
    (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
    (dgModuleNaturalConeArrow R D (CF) (U) (j) x)
    (dgModuleNaturalConeConnecting_arrow R D F G η x)
    (dgModuleNaturalConeRotationHom_arrow R D F G η x)
    (dgModuleNaturalConeInr_arrow R D G (CF) (ν) x)

end SerrePositivity.KST.SConstruction
