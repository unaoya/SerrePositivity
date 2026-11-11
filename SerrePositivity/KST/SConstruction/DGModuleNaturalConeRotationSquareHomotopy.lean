module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationSquare

/-!
概要：元全回転ホモトピーを同じ実 square の加群ホモトピーとして保持する。
方針：指定微分境界を使い、恒等との合成だけを同じ終辺へ輸送する。
規約：元次数 −1 元を保持。使われ方：元 connecting cone 射の指定 square 入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma transportVal {M N : ModuleCategory R D} (f g g' : M ⟶ N)
    (e : g = g') (h : ModuleHomotopy R D f g) :
    (e ▸ h : ModuleHomotopy R D f g').val = h.val := by
  cases e
  rfl
variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (CF) (ν)
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "γ" => dgModuleNaturalConeRotationHom R D F G η
local notation "j" => dgModuleNaturalConeInr R D G (CF) (ν)

/-- 概要：同じ元二辺・恒等・二重包含の実 square の指定ホモトピー。
方針：同じ全自然な次数 −1 元と実証済み微分境界を束ねる。
規約：元ホモトピーを選び直さない。使われ方：同じ元 connecting cone map の入力。 -/
def dgModuleNaturalConeRotationSquareHomotopy (x : P) :
    ModuleHomotopy R D
      (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x ≫
        dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
      ((𝟙 (ForgetEnrichment.of (Complex R) ((CF).obj x))) ≫
        dgModuleNaturalConeArrow R D (CF) (U) (j) x) :=
  (Category.id_comp (dgModuleNaturalConeArrow R D (CF) (U) (j) x)).symm ▸
    (⟨dgModuleNaturalConeRotationHomotopyElement R D F G η x,
      dgModuleNaturalConeRotationSquare_boundary R D F G η x⟩ : ModuleHomotopy R D
        (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x ≫
          dgModuleNaturalConeArrow R D (FS) (U) (γ) x)
        (dgModuleNaturalConeArrow R D (CF) (U) (j) x))

/-- 概要：同じ square ホモトピーの斉次元は元全自然な指定回転元そのもの。
方針：恒等合成の証拠輸送は斉次元を変えない。
規約：全自然性を元成分で回収する。使われ方：元 cone map 入力の全次数自然性。 -/
lemma dgModuleNaturalConeRotationSquareHomotopy_val (x : P) :
    (dgModuleNaturalConeRotationSquareHomotopy R D F G η x).val =
      dgModuleNaturalConeRotationHomotopyElement R D F G η x :=
  transportVal R D _ _ _
    (Category.id_comp (dgModuleNaturalConeArrow R D (CF) (U) (j) x)).symm
    ⟨dgModuleNaturalConeRotationHomotopyElement R D F G η x,
      dgModuleNaturalConeRotationSquare_boundary R D F G η x⟩
end SerrePositivity.KST.SConstruction
