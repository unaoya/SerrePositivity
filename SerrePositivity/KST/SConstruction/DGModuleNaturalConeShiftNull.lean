module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftArrow
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeNullHomotopy

/-!
概要：元 cone の指定零化元を整数 shift 後も全自然な指定元として保持する。
方針：元の符号付き自然性を同じ dg shift の全 Hom 作用で写す。
規約：元次数 −1 元と符号を保持する。
使われ方：実 cone と shift の比較の全自然性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma mapNegativeNaturality {R : Type u} [CommRing R]
    {C : Type v} {E : Type w} [DGCategory R C] [DGCategory R E]
    (Q : DGFunctor R C E) {A B A' B' : C}
    (a : GradedHom R A B (-1)) (a' : GradedHom R A' B' (-1))
    {n : ℤ} (f : GradedHom R A A' n) (g : GradedHom R B B' n)
    (h : compose R g a (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R a' f (sub_eq_add_neg n 1).symm) :
    compose R ((Q.map B B').f n g) ((Q.map A B).f (-1) a) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R ((Q.map A' B').f (-1) a') ((Q.map A A').f n f)
        (sub_eq_add_neg n 1).symm := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose Q g a (neg_add_eq_sub 1 n)).symm.trans
    ((congrArg ((Q.map A B').f (n - 1)) h).trans
      ((by simp only [Units.smul_def, map_zsmul] :
        (Q.map A B').f (n - 1)
          (n.negOnePow • compose R a' f (sub_eq_add_neg n 1).symm) =
        n.negOnePow • (Q.map A B').f (n - 1)
          (compose R a' f (sub_eq_add_neg n 1).symm)).trans
        (congrArg (fun t => n.negOnePow • t)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose Q a' f (sub_eq_add_neg n 1).symm))))
/-- 概要：符号付き次数 −1 全自然性を同じ dg 関手の全 Hom 作用で写す。
方針：元 shift 入力で使用した同じ合成保存の計算を適用する。
規約：元斉次元と指定符号を保持。使われ方：元実 cone の realization 全比較。 -/
lemma dgNegativeNaturalityMap {R : Type u} [CommRing R]
    {C : Type v} {E : Type w} [DGCategory R C] [DGCategory R E]
    (Q : DGFunctor R C E) {A B A' B' : C}
    (a : GradedHom R A B (-1)) (a' : GradedHom R A' B' (-1))
    {n : ℤ} (f : GradedHom R A A' n) (g : GradedHom R B B' n)
    (h : compose R g a (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R a' f (sub_eq_add_neg n 1).symm) :
    compose R ((Q.map B B').f n g) ((Q.map A B).f (-1) a) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R ((Q.map A' B').f (-1) a') ((Q.map A A').f n f)
        (sub_eq_add_neg n 1).symm := by
  exact mapNegativeNaturality Q a a' f g h
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：同じ元零化元の実 dg shift 像。
方針：元 shift の全 Hom 射を適用。
規約：次数 −1 を保持。使われ方：実 cone shift 比較の指定入力。 -/
def dgModuleNaturalConeShiftNull (s : ℤ) (x : P) :
    (moduleHom R D (shiftModule s (F.obj x)) (shiftModule s ((CF).obj x))).X (-1) :=
  (moduleShiftHom R D s (F.obj x) ((CF).obj x)).f (-1)
    (dgModuleNaturalConeNullHomotopyElement R D F G η x)

/-- 概要：同じ実 shift 後の指定零化元は全次数で符号付き自然。
方針：元全自然性を同じ dg shift の合成保存で写す。
規約：元整数次数・符号を保持。使われ方：元 cone shift 比較の全厳密化。 -/
lemma dgModuleNaturalConeShiftNull_naturality (s : ℤ) (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := shiftModule s (F.obj x)) (y := shiftModule s ((CF).obj x))
      (z := shiftModule s ((CF).obj y))
      ((((CF).comp (moduleShiftDG R D s)).map x y).f n z)
      (dgModuleNaturalConeShiftNull R D F G η s x) (neg_add_eq_sub 1 n) =
    n.negOnePow • compose R (x := shiftModule s (F.obj x)) (y := shiftModule s (F.obj y))
      (z := shiftModule s ((CF).obj y)) (dgModuleNaturalConeShiftNull R D F G η s y)
      (((F.comp (moduleShiftDG R D s)).map x y).f n z) (sub_eq_add_neg n 1).symm :=
  mapNegativeNaturality (moduleShiftDG R D s)
    (dgModuleNaturalConeNullHomotopyElement R D F G η x)
    (dgModuleNaturalConeNullHomotopyElement R D F G η y)
    ((F.map x y).f n z) (((CF).map x y).f n z)
    (dgModuleNaturalConeNullHomotopyElement_naturality R D F G η x y n z)
end SerrePositivity.KST.SConstruction
