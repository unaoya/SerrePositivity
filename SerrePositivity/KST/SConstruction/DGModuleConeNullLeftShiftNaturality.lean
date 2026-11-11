module
public import SerrePositivity.KST.SConstruction.DGConeNullLeftShiftNaturality

/-!
概要：元零化元の始域 shift の全自然性を実加群 Hom end に持ち上げる。
方針：元加群成分の始域 shift と全 Hom shift を各評価で照合する。
規約：元次数 −1 元の指定成分を保持。
使われ方：回転比較の同じ左包含を全関手族として構成する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元次数 −1 加群比較の符号付き自然性は始域 shift 後の次数零自然性を与える。
方針：各評価で同じ cochain の始域 shift の計算を使う。
規約：同じ全 Hom 要素を保持。使われ方：回転比較の元第二成分の自然性。 -/
lemma dgModuleConeNullLeftShift_naturality {M N M' N' : RightModule R D} {n : ℤ}
    (a : (moduleHom R D M M').X n) (b : (moduleHom R D N N').X n)
    (z : (moduleHom R D M N).X (-1)) (z' : (moduleHom R D M' N').X (-1))
    (h : compose R (x := M) (y := N) (z := N') b z (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R (x := M) (y := M') (z := N') z' a (sub_eq_add_neg n 1).symm) :
    compose R (x := shiftModule 1 M) (y := N) (z := N') b
        (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1) z) (zero_add n) =
      compose R (x := shiftModule 1 M) (y := shiftModule 1 M') (z := N')
        (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1) z')
        ((moduleShiftHom R D 1 M M').f n a) (add_zero n) := by
  apply moduleHomElement_ext R D
  intro e
  have he := congrArg ((moduleHomπ R D M N' e).f (n - 1)) h
  rw [moduleHomCompose_π, Units.smul_def, map_zsmul, moduleHomCompose_π] at he
  rw [moduleHomCompose_π, moduleHomLeftShiftElement_π,
    moduleHomCompose_π, moduleHomLeftShiftElement_π, moduleShiftHomElement_π]
  exact (dgConeNullLeftShift_naturality _ _ _ _ he).trans
    (congrArg (fun t => t.comp
      (((moduleHomπ R D M' N' e).f (-1) z').leftShift 1 0 (neg_add_cancel 1))
      (add_zero n)) (shiftHom_apply 1 (M.obj (Opposite.op e)) (M'.obj (Opposite.op e)) n
        ((moduleHomπ R D M M' e).f n a)))

variable {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η

/-- 概要：同じ実 cone の元左包含は始域 shift 後に全次数で次数零自然になる。
方針：元指定零化元の符号付き自然性を同じ加群 shift 計算へ適用する。
規約：左包含の閉性を主張しない。使われ方：回転比較関手族の第二成分。 -/
lemma dgModuleNaturalConeLeftShiftNull_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (F.comp (moduleShiftDG R D 1)).obj x) (y := (T).obj x) (z := (T).obj y)
      (((T).map x y).f n z)
      (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η x)) (zero_add n) =
    compose R (x := (F.comp (moduleShiftDG R D 1)).obj x)
      (y := (F.comp (moduleShiftDG R D 1)).obj y) (z := (T).obj y)
      (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η y))
      (((F.comp (moduleShiftDG R D 1)).map x y).f n z) (add_zero n) :=
  dgModuleConeNullLeftShift_naturality R D ((F.map x y).f n z) (((T).map x y).f n z)
    (dgModuleNaturalConeNullHomotopyElement R D F G η x)
    (dgModuleNaturalConeNullHomotopyElement R D F G η y)
    (dgModuleNaturalConeNullHomotopyElement_naturality R D F G η x y n z)
end SerrePositivity.KST.SConstruction
