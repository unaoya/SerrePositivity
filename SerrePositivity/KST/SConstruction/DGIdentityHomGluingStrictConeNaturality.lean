module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingModuleConeFamily
public import SerrePositivity.KST.SConstruction.DGModuleConeInputIsoFamilyNaturality

/-!
概要：元 gluing cone 入力の指定実同型を全次数自然な比較へ束ねる。
方針：元二軸・零第三成分の全 Hom 回収と同じ cone 入力等号を使う。
規約：元指定入力同型を変更しない。
使われ方：全実逆回転比較を元厳密 gluing 始域へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma fullHomNaturalityOfCycle {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] [Small.{u} C] {T : Type w} [DGCategory R T]
    (F G : DGFunctor R T (RightModule R C))
    (q : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y (n : ℤ) (z : (homObject R T x y).X n),
      compose R (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (q y))).val
        ((F.map x y).f n z) (add_zero n) =
      compose R ((G.map x y).f n z)
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (q x))).val (zero_add n))
    (x y : T) :
    F.map x y ≫ eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (q y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (q x)
        (ForgetEnrichment.of (Complex R) (G.obj y)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPostcompose_apply R C (q y) ((F.map x y).f n z)).trans
    ((h x y n z).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPrecompose_apply R C (q x) ((G.map x y).f n z)).symm)

private lemma factoryCycle {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] [Small.{u} C] {T : Type w} [DGCategory R T]
    (F G : DGFunctor R T (RightModule R C))
    (q : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (q y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (q x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (x : T) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C q h).app x =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (q x)) := rfl

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "c" => dgModuleNaturalConeArrow R C (F.comp (J)) (G.comp (J)) (η)
local notation "d" => dgHomGluingTargetModuleMap R C C C (I) (I)

/-- 概要：同じ元入力同型の始終を実全関手族の型で明示する。
方針：元二閉射の回収等号を同じ実 cone に適用する。
規約：同じ元入力等号で定義。使われ方：全比較の型を固定する指定同型。 -/
def dgIdentityHomGluingStrictConeTypedInputIso (x : P) :
    ForgetEnrichment.of (Complex R) ((A).obj x) ≅
      ForgetEnrichment.of (Complex R) ((B).obj x) :=
  eqToIso (congrArg (fun t => moduleCone R C t)
    ((dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h x).trans
      (dgIdentityHomGluingTargetModuleMap R C F G a h x).symm))

/-- 概要：実族の型を明示した入力同型は元指定入力同型そのもの。
方針：同じ cone 入力等号の証拠不可識別性を使う。
規約：元公開同型を変更しない。使われ方：元指定成分の厳密回収。 -/
lemma dgIdentityHomGluingStrictConeTypedInputIso_original (x : P) :
    HEq (dgIdentityHomGluingStrictConeTypedInputIso R C F G a h x)
      (dgIdentityHomGluingStrictConeInputIso R C F G a h x) := by rfl

local notation "e" => dgIdentityHomGluingStrictConeTypedInputIso R C F G a h

/-- 概要：元指定入力同型の同じ閉射を全関手族の型で保持する。
方針：元同型の順射を取る。
規約：元実閉射不変。使われ方：既存の厳密自然比較構成子の成分族。 -/
def dgIdentityHomGluingStrictConeInputMap (x : P) :
    ForgetEnrichment.of (Complex R) ((A).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((B).obj x) := (e x).hom

/-- 概要：元指定入力同型の同じ閉零成分。
方針：始終の全加群型を明示して閉元へ移す。
規約：元実入力同型を保持。使われ方：全厳密入力比較の成分。 -/
def dgIdentityHomGluingStrictConeInputComponent (x : P) :
    zeroCycles (moduleHom R C ((A).obj x) ((B).obj x)) :=
  cycleFromUnit (moduleHom R C ((A).obj x) ((B).obj x))
    (ForgetEnrichment.homTo (Complex R) (dgIdentityHomGluingStrictConeInputMap R C F G a h x))

/-- 概要：同じ元入力 cone 同型は元始域の全 Hom 作用と可換。
方針：同じ二入力等号と元二軸・零第三成分の回収を使う。
規約：全整数次数と元指定同型を保持。使われ方：元入力同型の全厳密化。 -/
lemma dgIdentityHomGluingStrictConeInputIso_naturality (x y : P) (n : ℤ)
    (z : (homObject R P x y).X n) :
    compose R (x := (A).obj x) (y := (A).obj y) (z := (B).obj y)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (e y).hom)).val
      (((A).map x y).f n z) (add_zero n) =
    compose R (x := (A).obj x) (y := (B).obj x) (z := (B).obj y)
      (((B).map x y).f n z)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (e x).hom)).val (zero_add n) := by
  have hs := dgModuleNaturalConeHomMap_apply R C (F.comp (J)) (G.comp (J)) (η) x y n z
  have ht := dgIdentityHomGluingModuleConeFamily_map R C F G a h x y n z
  exact dgModuleConeInputIso_family_naturality R C (c x) (d ((H).obj x))
    (c y) (d ((H).obj y))
    ((dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h x).trans
      (dgIdentityHomGluingTargetModuleMap R C F G a h x).symm)
    ((dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h y).trans
      (dgIdentityHomGluingTargetModuleMap R C F G a h y).symm)
    (e x) (e y) rfl rfl n (((F.comp (J)).map x y).f n z)
    (((G.comp (J)).map x y).f n z) (((A).map x y).f n z) (((B).map x y).f n z) hs ht

/-- 概要：元指定閉射族は全 Hom 鎖写像について自然。
方針：元全次数の斉次自然性を同じ閉射の前後合成へ戻す。
規約：元全鎖写像・閉射を保持。使われ方：既存の厳密比較構成子の全自然性。 -/
lemma dgIdentityHomGluingStrictConeInputMap_naturality (x y : P) :
    (A).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((A).obj x))
      (dgIdentityHomGluingStrictConeInputMap R C F G a h y) =
    (B).map x y ≫ eHomWhiskerRight (Complex R)
      (dgIdentityHomGluingStrictConeInputMap R C F G a h x)
      (ForgetEnrichment.of (Complex R) ((B).obj y)) :=
  fullHomNaturalityOfCycle (A) (B) (dgIdentityHomGluingStrictConeInputMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputIso_naturality R C F G a h) x y

/-- 概要：元 gluing cone 入力の同じ実同型を保持する全厳密比較。
方針：元指定閉射と全 Hom 自然性を既存の構成子へ渡す。
規約：元入力同型を選び直さない。使われ方：全実逆回転の元 cone 始域輸送。 -/
def dgIdentityHomGluingStrictConeInputComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (A) (B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C
    (dgIdentityHomGluingStrictConeInputMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputMap_naturality R C F G a h)

/-- 概要：元全入力比較の成分は同じ指定閉射の cycle。
方針：既存の構成子の成分を回収する。
規約：元閉射不変。使われ方：既存の native 全比較 API の入力。 -/
lemma dgIdentityHomGluingStrictConeInputComparison_cycle (x : P) :
    (dgIdentityHomGluingStrictConeInputComparison R C F G a h).app x =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgIdentityHomGluingStrictConeInputMap R C F G a h x)) :=
  factoryCycle (A) (B) (dgIdentityHomGluingStrictConeInputMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputMap_naturality R C F G a h) x
end SerrePositivity.KST.SConstruction
