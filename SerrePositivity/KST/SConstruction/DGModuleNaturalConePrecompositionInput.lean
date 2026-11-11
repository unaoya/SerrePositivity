module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationPrimitive
public import SerrePositivity.KST.SConstruction.DGModuleConeHomotopyIdentityInput

/-!
概要：指定した全厳密合成の cone 比較に使う零化入力を保持する。
方針：後の cone の元左包含を前の全厳密比較で前合成する。
規約：元包含・元比較・零ホモトピーを保持する。
使われ方：元 gluing の入力同型を保つ connecting cone の全比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
local notation "γ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α β
local notation "CB" => dgModuleNaturalConeFunctor R D G H β
local notation "a" => dgModuleNaturalConeArrow R D F G α
local notation "b" => dgModuleNaturalConeArrow R D G H β
local notation "c" => dgModuleNaturalConeArrow R D F H (γ)

/-- 概要：全厳密合成の元閉射による square の零ホモトピー。
方針：同じ全比較の閉成分の合成則を使用する。
規約：元合成を変更しない。使われ方：指定 cone 射の実 square。 -/
def dgModuleNaturalConePrecompositionSquareHomotopy (x : P) :
    ModuleHomotopy R D ((c x) ≫ 𝟙 _) ((a x) ≫ (b x)) :=
  ⟨0, by rw [Category.comp_id, dgModuleNaturalConeArrow_comp]; simp⟩

/-- 概要：元左包含を指定入力比較で前合成した零化元。
方針：閉零次数の指定成分との斉次合成を取る。
規約：元次数 −1 を保持。使われ方：同じ実 cone 比較の全自然性。 -/
def dgModuleNaturalConePrecompositionInput (x : P) :
    (moduleHom R D (F.obj x) ((CB).obj x)).X (-1) :=
  compose R (dgModuleNaturalConeNullHomotopyElement R D G H β x)
    (α.app x).val (zero_add (-1))

/-- 概要：指定前合成入力は全 Hom で符号付きに自然。
方針：元包含の符号付き自然性と指定前比較の全自然性を合成。
規約：閉零次数に制限しない。使われ方：cone descent の全自然性。 -/
lemma dgModuleNaturalConePrecompositionInput_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (((CB).map x y).f n z)
      (dgModuleNaturalConePrecompositionInput R D F G H α β x) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R
        (dgModuleNaturalConePrecompositionInput R D F G H α β y)
        ((F.map x y).f n z) (sub_eq_add_neg n 1).symm := by
  exact dgNegativeNaturalPrecomposition (α.app x).val
    (dgModuleNaturalConeNullHomotopyElement R D G H β x) (α.app y).val
    (dgModuleNaturalConeNullHomotopyElement R D G H β y)
    ((F.map x y).f n z) ((G.map x y).f n z) (((CB).map x y).f n z)
    (α.naturality z) (dgModuleNaturalConeNullHomotopyElement_naturality R D G H β x y n z)

/-- 概要：指定零化元は元零ホモトピー square の同じ cone 入力。
方針：零成分を除き、元閉射の前合成を斉次合成として回収する。
規約：指定入力を変更しない。使われ方：実 cone map の閉成分回収。 -/
lemma dgModuleNaturalConePrecompositionInput_recovery (x : P) :
    dgModuleNaturalConePrecompositionInput R D F G H α β x =
      moduleConeHomotopyInput R D (c x) (b x) (a x) (𝟙 _)
        (dgModuleNaturalConePrecompositionSquareHomotopy R D F G H α β x) := by
  dsimp only [moduleConeHomotopyInput, dgModuleNaturalConePrecompositionSquareHomotopy]
  change _ = _ + ((eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (F.obj x)) (moduleConeInr R D (b x))).f (-1)).hom 0
  rw [map_zero, add_zero]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPrecompose_apply R D (a x)
    (dgModuleNaturalConeNullHomotopyElement R D G H β x)).trans
      (congrArg (fun t => compose R
        (dgModuleNaturalConeNullHomotopyElement R D G H β x) t (zero_add (-1)))
        (dgModuleNaturalConeArrow_cycle R D F G α x)) |>.symm
end SerrePositivity.KST.SConstruction
