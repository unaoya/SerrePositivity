module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInput
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyIdentityInput

/-!
概要：全自然な回転入力を元の同じ実 square の cone 入力として回収する。
方針：元ホモトピー元と元右包含 cycle の回収を代入する。
規約：元実 square と全符号を保持する。
使われ方：元 connecting cone map を全厳密比較へ束ねる。
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

/-- 概要：同じ全自然な回転入力は元実 square の指定 cone 入力そのもの。
方針：恒等 square の計算と元包含・ホモトピーの回収を合わせる。
規約：点ごとに別のホモトピーを選ばない。使われ方：実 cone map の回収。 -/
lemma dgModuleNaturalConeRotationInput_recovery (x : P) :
    dgModuleNaturalConeRotationInput R D F G η x =
      moduleConeHomotopyInput R D
        (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x)
        (dgModuleNaturalConeArrow R D (CF) (U) (j) x)
        (𝟙 (ForgetEnrichment.of (Complex R) ((CF).obj x)))
        (dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
        (dgModuleNaturalConeRotationSquareHomotopy R D F G η x) := by
  rw [dgModuleConeHomotopyIdentityInput,
    dgModuleNaturalConeRotationSquareHomotopy_val]
  dsimp only [dgModuleNaturalConeRotationInput,
    dgModuleNaturalConeNullHomotopyElement]
  exact congrArg (fun t => moduleConeInlElement R D
    (dgModuleNaturalConeArrow R D (CF) (U) (j) x) + t)
    (congrArg (fun t => compose R (x := (CF).obj x) (y := (U).obj x) (z := (V).obj x)
      t (dgModuleNaturalConeRotationHomotopyElement R D F G η x) (add_zero (-1)))
      ((dgModuleNaturalConeArrow_cycle R D (U) (V) (k) x).symm.trans
        (congrArg (fun t => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) t)).val)
          (dgModuleNaturalConeInr_arrow R D (CF) (U) (j) x))))
end SerrePositivity.KST.SConstruction
