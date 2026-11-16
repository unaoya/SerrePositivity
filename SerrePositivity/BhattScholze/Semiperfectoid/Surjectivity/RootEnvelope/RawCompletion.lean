module

public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.RootEnvelope.Source
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-!
# raw 根環の逐次完備化

## 概要
raw r/d 包の A 作用と prism 候補への導来源射、raw 根環の逐次完備化と元の A 上の対象の比較、H⁰ の二座標反射と PD 完備化環。
BS 著者版 Theorem 7.4 の根の包による別証明に使う、raw 根環の逐次完備化を扱う。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`RootEnvelope/PerfectPrism`。
-/

universe u

/-! ## raw r/d包の標準A作用と既存prism候補への実導来源射 -/

@[expose] public noncomputable section DeltaRootSourceRawCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "β" => deltaDivisionSourceEval E r
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "C₀" => algebraMap A L

/-- 評価βを経由する制限作用と、raw環の標準A作用の恒等線形同型。 -/
def Semiperfectoid.deltaRootSourceRawCoefficientModuleIso :
    (ModuleCat.restrictScalars C₀).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b) ≅
      ModuleCat.of A Raw := by
  let e : (ModuleCat.restrictScalars C₀).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b) ≃ₗ[A] Raw :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
        change Raw at x
        change j (β (MvPolynomial.C (MvPolynomial.C a))) * x = a • x
        rw [Algebra.smul_def, _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_C]
        rfl }
  exact e.toModuleIso

/-- 元のAへの実係数制限後のraw対象を、標準A作用付きraw環の次数零対象へ戻す。 -/
def Semiperfectoid.deltaRootSourceRawCoefficientSingleIso :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Raw) :=
  ObjectProperty.isoMk _
    ((_root_.SerrePositivity.derivedRestrictScalarsSingleIso C₀ 0).app (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientModuleIso D d b))

set_option maxHeartbeats 800000 in
-- Keep the original derived tensor and both coefficient restrictions explicit in H0.
/-- 元の実導来源のH0は、標準A作用付きraw r/d環と線形同型。 -/
def Semiperfectoid.deltaRootSourceRawStandardH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b).obj ≅ ModuleCat.of A Raw :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientH0Iso D d b ≪≫ _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientModuleIso D d b

/-- 既存prism台環候補の標準係数射によるA代数構造。 -/
abbrev Semiperfectoid.deltaRootPrismCoefficientAlgebra :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    Algebra A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b).toAlgebra

/-- 既存raw環射は、元のAの標準係数作用について線形。 -/
def Semiperfectoid.deltaRootSourceRawCandidateLinearMap :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientAlgebra D d b
    letI : Module A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := Algebra.toModule
    Raw →ₗ[A] _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact
    { toFun := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b
      map_add' := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b).map_add
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        change _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b (algebraMap A Raw a * x) =
          _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b a * _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b x
        rw [map_mul]
        rfl }

/-- 既存候補台環を、標準A係数作用で次数零に置いた実導来対象。 -/
abbrev Semiperfectoid.DeltaRootPrismCoefficientObject : DerivedCategory.Minus (ModuleCat.{u} A) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b))

/-- 元の実二因子導来源から、既存候補の実次数零対象への標準比較射。 -/
def Semiperfectoid.deltaRootSourceCandidateMap :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b ⟶ _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCoefficientObject D d b := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b ≫
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientSingleIso D d b).hom ≫
    _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.map
      (ModuleCat.ofHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCandidateLinearMap D d b))

end SerrePositivity.BhattScholze

end DeltaRootSourceRawCoefficients

/-! ## raw根環自身の実逐次完備化と元のA上の実対象の比較 -/

@[expose] public noncomputable section DeltaRootRawCompletionRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor A (p : A)
local notation "Cd" => derivedComplexCompletionFunctor A d
local notation "Bp" => derivedComplexCompletionFunctor Raw (c (p : A))
local notation "Bd" => derivedComplexCompletionFunctor Raw (c d)
local notation "Res" => derivedRestrictScalars c

/-- 元のraw係数対象は、raw環自身のsingleを実係数射で制限した対象。 -/
def Semiperfectoid.deltaRootRawCoefficientRestrictionIso :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientSingleIso D d b) ≪≫
    (_root_.SerrePositivity.algebraRestrictionSingleIso A Raw).symm

/-- raw環自身の二つの主元についての実逐次完備化。 -/
abbrev Semiperfectoid.DeltaRootRawInternalIteratedCompletion := (Bd).obj ((Bp).obj M)

/-- 二度の係数制限と完備化の比較を同じ係数射に適用した、元のraw実逐次対象との同型。 -/
def Semiperfectoid.deltaRootRawIteratedRestrictionIso :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawIteratedCompletion D d b).obj ≅
      (Res).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion D d b) :=
  (Cd).mapIso ((Cp).mapIso (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawCoefficientRestrictionIso D d b)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 係数比較は両方の元の主元完備化単位を保つ。 -/
theorem Semiperfectoid.deltaRootRawIteratedRestrictionIso_unit :
    ((derivedComplexCompletionUnit A (p : A)).app
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj)) ≫
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawIteratedRestrictionIso D d b).hom =
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawCoefficientRestrictionIso D d b).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawCoefficientRestrictionIso D d b
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawIteratedRestrictionIso D d b).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawIteratedRestrictionIso, eP, e, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedComplexCompletionUnit A d).app _) ((Cd).map eP.hom),
    ← hd]
  simp only [Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

/-- raw環上の同じ実逐次完備化のH0へ、元のA作用を保って比較する。 -/
def Semiperfectoid.deltaRootRawIteratedRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawIteratedCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion D d b)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawIteratedRestrictionIso D d b) ≪≫
      (_root_.SerrePositivity.derivedRestrictScalarsHomologyIso c 0).app _

/-- 元の実根添加源のH0をraw環上の実逐次完備化のH0と同定する。 -/
def Semiperfectoid.deltaRootSourceInternalRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion D d b)) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedH0Iso D d b ≪≫ _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawIteratedRestrictionH0Iso D d b

end SerrePositivity.BhattScholze

end DeltaRootRawCompletionRestriction

/-! ## raw根環の実逐次完備化H0の二座標反射 -/

@[expose] public noncomputable section DeltaRootRawCompletionReflection

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "a" => (c (p : A))
local notation "z" => (c d)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor Raw a
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor Raw a) M
local notation "Z" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion D d b
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw a) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw z) Y

/-- raw自身の実逐次完備化から誘導される、元のRaw線形標準単位。 -/
def Semiperfectoid.deltaRootRawInternalH0Unit : Raw →ₗ[Raw] H Z :=
  (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Raw) 0).inv.app
    (ModuleCat.of Raw Raw)) ≫ (DerivedCategory.homologyFunctor (ModuleCat Raw) 0).map U).hom

/-- raw自身の実逐次対象は、二つ目の完備化後にも最初の座標について完備。 -/
theorem Semiperfectoid.deltaRootRawInternalIterated_isComplete_first : IsComplete Raw a Z := by
  exact _root_.SerrePositivity.DerivedCompletion.iteratedPDCompletion_isComplete_first Raw a z

/-- raw自身の実逐次H0は両座標について導来完備。 -/
theorem Semiperfectoid.deltaRootRawInternalH0_isComplete :
    ∀ j : Fin 2, IsModuleComplete Raw (pairKoszulCoordinates Raw a z j) (H Z) := by
  exact _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isComplete Raw a z

/-- 同じ標準単位は、両座標について完備な加群への写像を一意に決定する。 -/
theorem Semiperfectoid.deltaRootRawInternalH0_isCompleteModuleReflection :
    IsCompleteModuleReflection Raw (pairKoszulCoordinates Raw a z) (H Z)
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit D d b 1) := by
  simpa only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit, _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion,
    _root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit] using _root_.SerrePositivity.DerivedCompletion.iteratedPDH0_isCompleteModuleReflection Raw a z

/-- 二つの実H0反射の間には、元の線形標準単位を保つ同型がある。 -/
theorem Semiperfectoid.exists_deltaRootRawInternalPDLinearEquiv :
    ∃ e : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z,
      ∀ x : Raw, e (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit D d b x) =
        pairCompletionH0Unit Raw (p : Raw) z x := by
  simpa only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit, _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion,
    _root_.SerrePositivity.DerivedCompletion.iteratedPDH0Unit] using
      _root_.SerrePositivity.DerivedCompletion.exists_iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 元のRaw線形単位で正規化した、実逐次H0から実PD完備化H0への同型。 -/
def Semiperfectoid.deltaRootRawInternalPDLinearEquiv : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_deltaRootRawInternalPDLinearEquiv D d b).choose

/-- 比較は全raw係数の元の完備化像を保つ。 -/
theorem Semiperfectoid.deltaRootRawInternalPDLinearEquiv_unit (x : Raw) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv D d b (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit D d b x) =
      pairCompletionH0Unit Raw (p : Raw) z x :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_deltaRootRawInternalPDLinearEquiv D d b).choose_spec x

/-- 元の実根添加源の実H0とrawのPD完備化H0の具体的A線形同型。 -/
def Semiperfectoid.deltaRootSourcePDH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceInternalRawH0Iso D d b ≪≫
    (ModuleCat.restrictScalars c).mapIso (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv D d b).toModuleIso

end SerrePositivity.BhattScholze

end DeltaRootRawCompletionReflection

/-! ## raw根環の実逐次H0の反射環とPD完備化環 -/

@[expose] public noncomputable section DeltaRootRawCompletedH0Ring

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "a" => (c (p : A))
local notation "z" => (c d)
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor Raw a
local notation "Y" => CategoryTheory.Functor.obj (derivedComplexCompletionFunctor Raw a) M
local notation "Z" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootRawInternalIteratedCompletion D d b
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)
local notation "U" => CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw a) M ≫
  CategoryTheory.NatTrans.app (derivedComplexCompletionUnit Raw z) Y

/-- 元の実逐次H0の加法とRaw作用を保つ反射環。 -/
@[instance_reducible] def Semiperfectoid.deltaRootRawInternalH0CommRing : CommRing (H Z) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0_isCompleteModuleReflection D d b).commRing

/-- 元の実Raw作用と一致する反射環の代数構造。 -/
@[instance_reducible] def Semiperfectoid.deltaRootRawInternalH0Algebra :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0CommRing D d b
    Algebra Raw (H Z) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0_isCompleteModuleReflection D d b).algebra

/-- 元の線形比較は、同じ反射環構造についてRaw代数同型である。 -/
def Semiperfectoid.deltaRootRawInternalPDAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0CommRing D d b
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Algebra D d b
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionAlgebra Raw p z
    H Z ≃ₐ[Raw] PDCompletionH0 Raw p z := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0CommRing D d b
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Algebra D d b
  letI := pdCompletionCommRing Raw p z
  letI := pdCompletionAlgebra Raw p z
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv D d b
  let h := pairCompletionH0_isCompleteModuleReflection Raw (p : Raw) z
  have hT : ∀ j : Fin 2, IsModuleComplete Raw
      (pairKoszulCoordinates Raw (p : Raw) z j) (H Z) := by
    simpa only [map_natCast] using _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0_isComplete D d b
  have h1 : e.symm (pairCompletionH0Unit Raw (p : Raw) z 1) = (1 : H Z) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv_unit D d b 1).symm
  exact (AlgEquiv.ofLinearEquiv e.symm h1
    (h.linearMap_map_mul (H Z) hT e.symm.toLinearMap h1)).symm

/-- 代数同型の関数は、元の標準単位で正規化した線形比較そのもの。 -/
theorem Semiperfectoid.deltaRootRawInternalPDAlgEquiv_apply (x : H Z) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDAlgEquiv D d b x = _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv D d b x := rfl

/-- 代数比較も、すべてのraw係数の元のPD完備化像を保つ。 -/
theorem Semiperfectoid.deltaRootRawInternalPDAlgEquiv_unit (x : Raw) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDAlgEquiv D d b (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalH0Unit D d b x) =
      pdCompletionUnit Raw p z x := by
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDAlgEquiv_apply, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootRawInternalPDLinearEquiv_unit,
    pdCompletionUnit_apply]

end SerrePositivity.BhattScholze

end DeltaRootRawCompletedH0Ring
