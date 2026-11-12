module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeLift
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv
public import SerrePositivity.KST.SConstruction.DGModuleClosedLeftShiftNaturality
public import SerrePositivity.KST.SConstruction.DGModuleConeNullLeftShiftNaturality
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-!
概要：元実回転比較の同じ第一・第二成分に全自然性と閉条件を与える。
方針：元閉比較と左包含の始域 shift の指定負符号を全 Hom 上で保持する。
規約：元回転成分を選び直さない。使われ方：同じ実全厳密回転比較の構成。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
private lemma composeNegLeft {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]
    {x y z : E} {p q n : ℤ} (g : GradedHom R y z q) (f : GradedHom R x y p)
    (hn : p + q = n) : compose R (-g) f hn = -compose R g f hn := by
  simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left (0 : GradedHom R y z q) g f hn
private lemma composeNegRight {R : Type u} [CommRing R] {E : Type v} [DGCategory R E]
    {x y z : E} {p q n : ℤ} (g : GradedHom R y z q) (f : GradedHom R x y p)
    (hn : p + q = n) : compose R g (-f) hn = -compose R g f hn := by
  simpa only [zero_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right g (0 : GradedHom R x y p) f hn

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "a" => dgModuleNaturalConeArrow R D F G η
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "ν" => dgModuleNaturalConeInr R D F G η

/-- 概要：元回転比較の第一成分は同じ元比較 cycle の始域 shift の負。
方針：同じ閉元の回収を元始域 shift に適用する。
規約：元負符号を保持。使われ方：第一成分の全自然性。 -/
lemma dgModuleNaturalConeRotationFirst_eq (x : P) :
    moduleConeRotationFirst R D (a x) =
      -moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app x).val :=
  congrArg (fun t => -moduleHomLeftShiftElement R D 1 (zero_add 1) t)
    (dgModuleNaturalConeArrow_cycle R D F G η x)

/-- 概要：元回転比較の第一成分は次数一の符号付き全自然性を満たす。
方針：同じ元閉比較の始域 shift 後の全自然性に負を適用する。
規約：元成分を保持。使われ方：実回転比較の全 cone lift の第一入力。 -/
lemma dgModuleNaturalConeRotationFirst_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (FS).obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z) (moduleConeRotationFirst R D (a x)) (add_comm 1 n) =
    n.negOnePow • compose R (x := (FS).obj x) (y := (FS).obj y) (z := G.obj y)
      (moduleConeRotationFirst R D (a y)) (((FS).map x y).f n z) rfl := by
  have hn := dgModuleStrictComparisonLeftShift_naturality R D F G η x y n z
  have he : compose R (x := (FS).obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z) (-moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app x).val)
      (add_comm 1 n) =
    n.negOnePow • compose R (x := (FS).obj x) (y := (FS).obj y) (z := G.obj y)
      (-moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app y).val)
      (((FS).map x y).f n z) rfl := by
    have hr := composeNegLeft (R := R) (E := RightModule R D)
      (moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app y).val)
      (((FS).map x y).f n z) rfl
    exact (composeNegRight (R := R) (E := RightModule R D)
      ((G.map x y).f n z)
      (moduleHomLeftShiftElement R D 1 (zero_add 1) (η.app x).val) (add_comm 1 n)).trans
      ((congrArg Neg.neg hn).trans
        ((congrArg (fun t => n.negOnePow • t) hr).trans (smul_neg _ _)).symm)
  exact (congrArg (fun t => compose R (x := (FS).obj x) (y := G.obj x) (z := G.obj y)
      ((G.map x y).f n z) t (add_comm 1 n))
      (dgModuleNaturalConeRotationFirst_eq R D F G η x)).trans
    (he.trans (congrArg (fun t => n.negOnePow • compose R
      (x := (FS).obj x) (y := (FS).obj y) (z := G.obj y) t (((FS).map x y).f n z) rfl)
      (dgModuleNaturalConeRotationFirst_eq R D F G η y)).symm)

/-- 概要：元第二成分は同じ元左包含の始域 shift の指定負。
方針：元定義を回収する。規約：元成分を保持。使われ方：全自然性の照合。 -/
lemma dgModuleNaturalConeRotationSecond_eq (x : P) :
    moduleConeRotationSecond R D (a x) =
      -moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η x) := rfl

/-- 概要：元回転比較の第二成分は次数零で全自然。
方針：同じ元左包含の始域 shift 後の自然性に指定負符号を付ける。
規約：元回転成分を保持。使われ方：実回転比較の全 cone lift の第二入力。 -/
lemma dgModuleNaturalConeRotationSecond_naturality (x y : P) (n : ℤ)
    (z : GradedHom R x y n) :
    compose R (x := (FS).obj x) (y := (CF).obj x) (z := (CF).obj y)
      (((CF).map x y).f n z) (moduleConeRotationSecond R D (a x)) (zero_add n) =
    compose R (x := (FS).obj x) (y := (FS).obj y) (z := (CF).obj y)
      (moduleConeRotationSecond R D (a y)) (((FS).map x y).f n z) (add_zero n) := by
  have hn := dgModuleNaturalConeLeftShiftNull_naturality R D F G η x y n z
  have he : compose R (x := (FS).obj x) (y := (CF).obj x) (z := (CF).obj y)
      (((CF).map x y).f n z)
      (-moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η x)) (zero_add n) =
    compose R (x := (FS).obj x) (y := (FS).obj y) (z := (CF).obj y)
      (-moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η y))
      (((FS).map x y).f n z) (add_zero n) :=
    (composeNegRight (R := R) (E := RightModule R D) (((CF).map x y).f n z)
      (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
        (dgModuleNaturalConeNullHomotopyElement R D F G η x)) (zero_add n)).trans
      ((congrArg Neg.neg hn).trans
        (composeNegLeft (R := R) (E := RightModule R D)
          (moduleHomLeftShiftElement R D 1 (neg_add_cancel 1)
            (dgModuleNaturalConeNullHomotopyElement R D F G η y))
          (((FS).map x y).f n z) (add_zero n)).symm)
  exact (congrArg (fun t => compose R (x := (FS).obj x) (y := (CF).obj x) (z := (CF).obj y)
      (((CF).map x y).f n z) t (zero_add n))
        (dgModuleNaturalConeRotationSecond_eq R D F G η x)).trans
    (he.trans (congrArg (fun t => compose R (x := (FS).obj x) (y := (FS).obj y) (z := (CF).obj y)
      t (((FS).map x y).f n z) (add_zero n))
        (dgModuleNaturalConeRotationSecond_eq R D F G η y)).symm)

/-- 概要：元二成分の閉条件は同じ実右包含族を使って成立する。
方針：元右包含回収を従来の実回転比較の閉条件へ代入する。
規約：元実 cone と指定二成分を保持。使われ方：全厳密回転比較の閉性。 -/
lemma dgModuleNaturalConeRotationHom_boundary (x : P) :
    (moduleHom R D ((FS).obj x) ((CF).obj x)).d 0 1
      (moduleConeRotationSecond R D (a x)) +
      (show (moduleHom R D ((FS).obj x) ((CF).obj x)).X 1 from
        (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((FS).obj x))
          (dgModuleNaturalConeArrow R D G (CF) (ν) x)).f 1
            (moduleConeRotationFirst R D (a x))) = 0 := by
  have he := congrArg (fun t => (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((FS).obj x)) t).f 1
        (moduleConeRotationFirst R D (a x))) (dgModuleNaturalConeInr_arrow R D F G η x)
  exact (congrArg (fun t =>
    (moduleHom R D ((FS).obj x) ((CF).obj x)).d 0 1
      (moduleConeRotationSecond R D (a x)) + t) he).trans
        (moduleConeRotationInputs_cycle R D (a x))
end SerrePositivity.KST.SConstruction
