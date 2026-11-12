module
public import SerrePositivity.KST.SConstruction.DGNegativeNaturalPostcomposition
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationSquareHomotopy

/-!
概要：元回転 square の cone 比較に用いる指定零化元を全次数で保持する。
方針：元左包含と指定ホモトピーの元右包含による後合成を足す。
規約：元回転の指定符号を保持する。
使われ方：元 connecting cone map の全厳密自然性。
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
local notation "κ" => dgModuleNaturalConeRotationHomotopyElement R D F G η

/-- 概要：同じ元左包含と回転ホモトピーからなる cone 射の指定入力元。
方針：元の二成分を変更せず加える。
規約：次数 −1 元を保持。使われ方：実 connecting cone 比較の指定零化。 -/
def dgModuleNaturalConeRotationInput (x : P) :
    (moduleHom R D ((CF).obj x) ((V).obj x)).X (-1) :=
  dgModuleNaturalConeNullHomotopyElement R D (CF) (U) (j) x +
    compose R (x := (CF).obj x) (y := (U).obj x) (z := (V).obj x)
      ((k).app x).val (κ x) (add_zero (-1))

/-- 概要：同じ指定零化入力は全 Hom に符号付きで自然。
方針：元左包含の自然性と回転ホモトピーの後合成自然性を足す。
規約：元の全整数次数を保持。使われ方：同じ実 cone 比較の全自然性。 -/
lemma dgModuleNaturalConeRotationInput_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (CF).obj x) (y := (V).obj x) (z := (V).obj y)
      (((V).map x y).f n z) (dgModuleNaturalConeRotationInput R D F G η x)
      (neg_add_eq_sub 1 n) =
    n.negOnePow • compose R (x := (CF).obj x) (y := (CF).obj y) (z := (V).obj y)
      (dgModuleNaturalConeRotationInput R D F G η y) (((CF).map x y).f n z)
      (sub_eq_add_neg n 1).symm := by
  have h₁ := dgModuleNaturalConeNullHomotopyElement_naturality R D (CF) (U) (j) x y n z
  have h₂ := dgNegativeNaturalPostcomposition
    (κ x) ((k).app x).val (κ y) ((k).app y).val
    (((CF).map x y).f n z) (((U).map x y).f n z) (((V).map x y).f n z)
    (dgModuleNaturalConeRotationHomotopyElement_naturality R D F G η x y n z)
    ((k).naturality z)
  dsimp only [dgModuleNaturalConeRotationInput]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right _ _ _ _).trans
    ((congrArg₂ (fun a b => a + b) h₁ h₂).trans
      ((smul_add _ _ _).symm.trans
        (congrArg (fun t => n.negOnePow • t) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left _ _ _ _).symm)))
end SerrePositivity.KST.SConstruction
