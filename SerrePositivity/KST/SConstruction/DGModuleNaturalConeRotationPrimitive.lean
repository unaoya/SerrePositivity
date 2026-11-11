module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRetraction

/-!
概要：元回転 cone の指定ホモトピーを構成する右射影・左包含の合成を全次数で保持する。
方針：元右射影の次数零自然性と元左包含の符号付き自然性を合成する。
規約：元厳密比較族上の同じ実二重 cone を使用する。
使われ方：実逆回転後の全比較の指定ホモトピー成分。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
private lemma compositeNaturality {R : Type u} [CommRing R]
    {D : Type v} [DGCategory R D] {U V W U' V' W' : D}
    (a : GradedHom R U V 0) (b : GradedHom R V W (-1))
    (a' : GradedHom R U' V' 0) (b' : GradedHom R V' W' (-1))
    {n : ℤ} (f : GradedHom R U U' n) (g : GradedHom R V V' n)
    (k : GradedHom R W W' n)
    (ha : compose R a' f (add_zero n) = compose R g a (zero_add n))
    (hb : compose R k b (by omega : -1 + n = n - 1) =
      n.negOnePow • compose R b' g (by omega : n + -1 = n - 1)) :
    compose R k (compose R b a (zero_add (-1))) (by omega : -1 + n = n - 1) =
      n.negOnePow • compose R (compose R b' a' (zero_add (-1))) f
        (by omega : n + -1 = n - 1) := by
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum a b k (zero_add (-1))
    (by omega : -1 + n = n - 1) (by omega : -1 + n = n - 1)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum a g b' (zero_add n)
    (by omega : n + -1 = n - 1) (by omega : n + -1 = n - 1)
  have h₃ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum f a' b' (add_zero n)
    (zero_add (-1)) (by omega : n + -1 = n - 1)
  calc
    _ = compose R (compose R k b (by omega)) a (zero_add (n - 1)) := h₁
    _ = compose R (n.negOnePow • compose R b' g (by omega)) a (zero_add (n - 1)) :=
      congrArg (fun t => compose R t a (zero_add (n - 1))) hb
    _ = n.negOnePow • compose R (compose R b' g (by omega)) a (zero_add (n - 1)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left _ _ _ _
    _ = n.negOnePow • compose R b' (compose R g a (zero_add n)) (by omega) :=
      congrArg (fun t => n.negOnePow • t) h₂.symm
    _ = n.negOnePow • compose R b' (compose R a' f (add_zero n)) (by omega) :=
      congrArg (fun t => n.negOnePow • compose R b' t (by omega)) ha.symm
    _ = _ := congrArg (fun t => n.negOnePow • t) h₃

/-- 概要：閉零次数比較による次数 −1 族の前合成は符号付きで全自然。
方針：元回転入力で使用した同じ結合則の補題へ渡す。
規約：元全次数と負符号を保持。使われ方：指定入力比較を保つ cone 全比較。 -/
lemma dgNegativeNaturalPrecomposition {R : Type u} [CommRing R]
    {D : Type v} [DGCategory R D] {U V W U' V' W' : D}
    (a : GradedHom R U V 0) (b : GradedHom R V W (-1))
    (a' : GradedHom R U' V' 0) (b' : GradedHom R V' W' (-1))
    {n : ℤ} (f : GradedHom R U U' n) (g : GradedHom R V V' n)
    (k : GradedHom R W W' n)
    (ha : compose R a' f (add_zero n) = compose R g a (zero_add n))
    (hb : compose R k b (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R b' g (sub_eq_add_neg n 1).symm) :
    compose R k (compose R b a (zero_add (-1))) (neg_add_eq_sub 1 n) =
      n.negOnePow • compose R (compose R b' a' (zero_add (-1))) f
        (sub_eq_add_neg n 1).symm := by
  exact compositeNaturality a b a' b' f g k ha hb

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "T" => dgModuleNaturalConeFunctor R D F G η
local notation "ν" => dgModuleNaturalConeInr R D F G η
local notation "U" => dgModuleNaturalConeFunctor R D G (T) (ν)

/-- 概要：同じ cone の右射影と次の cone の左包含を合成した次数 −1 元。
方針：元二つの指定成分をそのまま合成する。
規約：回転ホモトピーへの負符号は別途保持する。
使われ方：同じ二重 cone の全自然な回転ホモトピー成分。 -/
def dgModuleNaturalConeRotationPrimitive (x : P) :
    (moduleHom R D ((T).obj x) ((U).obj x)).X (-1) :=
  compose R (x := (T).obj x) (y := G.obj x) (z := (U).obj x)
    (dgModuleNaturalConeNullHomotopyElement R D G (T) (ν) x)
    (dgModuleNaturalConeRetractionElement R D F G η x) (zero_add (-1))

/-- 概要：同じ元回転ホモトピーの合成成分は全 Hom に符号付きで自然。
方針：次数零の右射影と次数 −1 の左包含の自然性を結合則で合成する。
規約：全次数を保ち、閉零次数だけの可換性に落とさない。
使われ方：実 connecting cone 比較の全自然性の指定成分。 -/
lemma dgModuleNaturalConeRotationPrimitive_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (T).obj x) (y := (U).obj x) (z := (U).obj y)
      (((U).map x y).f n z) (dgModuleNaturalConeRotationPrimitive R D F G η x)
      (by omega : -1 + n = n - 1) =
    n.negOnePow • compose R (x := (T).obj x) (y := (T).obj y) (z := (U).obj y)
      (dgModuleNaturalConeRotationPrimitive R D F G η y) (((T).map x y).f n z)
      (by omega : n + -1 = n - 1) := by
  dsimp only [dgModuleNaturalConeRotationPrimitive]
  exact compositeNaturality
    (dgModuleNaturalConeRetractionElement R D F G η x)
    (dgModuleNaturalConeNullHomotopyElement R D G (T) (ν) x)
    (dgModuleNaturalConeRetractionElement R D F G η y)
    (dgModuleNaturalConeNullHomotopyElement R D G (T) (ν) y)
    (((T).map x y).f n z) ((G.map x y).f n z) (((U).map x y).f n z)
    (dgModuleNaturalConeRetractionElement_naturality R D F G η x y n z)
    (dgModuleNaturalConeNullHomotopyElement_naturality R D G (T) (ν) x y n z)
/-- 概要：元回転ホモトピーの指定負符号を付けた同じ斉次元。
方針：元右射影・左包含の合成を負にする。
規約：次数 −1 の元を保持。使われ方：connecting cone の全比較の指定ホモトピー。 -/
def dgModuleNaturalConeRotationHomotopyElement (x : P) :
    (moduleHom R D ((T).obj x) ((U).obj x)).X (-1) :=
  -dgModuleNaturalConeRotationPrimitive R D F G η x

/-- 概要：指定負符号を含む元回転ホモトピーは全 Hom で符号付き自然。
方針：元合成成分の全自然性に負を適用し、合成の線形性を使う。
規約：元回転符号を保持。使われ方：指定ホモトピーから作る全 cone 比較。 -/
lemma dgModuleNaturalConeRotationHomotopyElement_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (T).obj x) (y := (U).obj x) (z := (U).obj y)
      (((U).map x y).f n z) (dgModuleNaturalConeRotationHomotopyElement R D F G η x)
      (by omega : -1 + n = n - 1) =
    n.negOnePow • compose R (x := (T).obj x) (y := (T).obj y) (z := (U).obj y)
      (dgModuleNaturalConeRotationHomotopyElement R D F G η y) (((T).map x y).f n z)
      (by omega : n + -1 = n - 1) := by
  dsimp only [dgModuleNaturalConeRotationHomotopyElement]
  simpa only [compose, forward, TensorProduct.tmul_neg, TensorProduct.neg_tmul,
    map_neg, smul_neg] using congrArg Neg.neg
      (dgModuleNaturalConeRotationPrimitive_naturality R D F G η x y n z)
end SerrePositivity.KST.SConstruction
