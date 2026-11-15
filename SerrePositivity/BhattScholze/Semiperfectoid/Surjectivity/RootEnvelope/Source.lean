module

public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.FamilyEvaluation
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.CommutativeAlgebra.Witt.Coefficients
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.PerfectPrismDivision
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.CompatibleRootPerfectoid
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.Surjectivity
public import SerrePositivity.BhattScholze.Perfectoidization.TensorPerfectoidization

/-!
# 根の割り算包の源（BS 著者版 Theorem 7.4 の別証明）

## 概要
有界深さの部分族図式の Tor 消滅、任意根族の全源 Tor 入力からの係数還元、商還元の純性と H⁰ の忠実平坦性、(p,d) 還元・逐次完備化後の還元、Tor 交換、根 δ 除算包の通常商の互換 p 冪根族、perfectoid 候補と基底射、直接 PD 完備化・δ 完全化との比較、生成元冪商の完備性、源の raw 比較・非正性・H⁰、完全 δ 環の rank-one 元の互換根列、根付き生成族による全射性とその降下。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`RootEnvelope/PerfectPrism`、`RootEnvelope/RawCompletion`。
-/

universe u v w z

/-! ## 有界深さ有限部分族図式の実残余Tor消滅 -/

@[expose] public noncomputable section DeltaDivisionBoundedSupportTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {σ : Type u}

private theorem Semiperfectoid.coordinate_range {m : ℕ} (T : Finset σ) (s : Fin m ≃ T) (N : ℕ) :
    Set.range (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N).get =
      {z : σ × ℕ | z.1 ∈ T ∧ z.2 ≤ N} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N _).mp (List.get_mem _ i)
    rw [← he]
    exact ⟨(s j).property, hk⟩
  · rintro ⟨hz, hn⟩
    obtain ⟨j, hj⟩ := s.surjective ⟨z.1, hz⟩
    have hm : z ∈ _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N :=
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N z).mpr
        ⟨j, z.2, hn, Prod.ext (congrArg Subtype.val hj) rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact ⟨i, hi⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) a
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "F" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E r
local notation "K" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationFiniteSupportIdeal E r

/-- 任意根族の有界深さ評価図式の全段は、元の実残余係数射に沿う正次数Torが零。 -/
theorem Semiperfectoid.deltaRootBoundedSupportStage_tor_subsingleton
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (S : Finset (σ × ℕ)) (i : ℕ) :
    Subsingleton (((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)).obj ((F).obj S)) := by
  classical
  let T := S.image Prod.fst
  let N := S.sup Prod.snd
  let s : Fin T.card ≃ T := (Finset.equivFin T).symm
  let cs := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (fun j => (s j : σ)) N
  have hcoords : Set.range cs.get = (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S : Set (σ × ℕ)) := by
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.coordinate_range T s N]
    ext z
    exact (_root_.SerrePositivity.BhattScholze.Andre.mem_deltaDivisionCoordinateHull S z).symm
  have hK : K (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S) =
      Ideal.span (Set.range fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r (cs.get j)) := by
    change Ideal.span (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r ''
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S : Set (σ × ℕ))) = _
    rw [← hcoords, ← Set.range_comp']
  let e : (F).obj S ≅
      ModuleCat.of L (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get) :=
    (Submodule.quotEquivOfEq _ _ (show (K (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionCoordinateHull S) : Submodule L L) =
      Ideal.span (Set.range fun j => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E r (cs.get j))
        from hK)).toModuleIso
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have ht := _root_.SerrePositivity.BhattScholze.Andre.deltaRootFiniteSubfamilySource_tor_subsingleton
    (T : Set σ) D d a s N hpA v hv i
  have hz : IsZero (H.obj
      (ModuleCat.of L (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get))) := by
    let := ht
    exact ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso (H.mapIso e))

/-- この実図式のTor交換入力の下で、任意根族の全β評価環の正次数Torが零。 -/
theorem Semiperfectoid.deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
  let := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F)) :=
    _root_.SerrePositivity.torAlg_finsetColimit_isZero_of_stages (σ × ℕ) ψ F (i + 1)
      (fun S => ModuleCat.isZero_iff_subsingleton.mpr
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportStage_tor_subsingleton D d a hpA v hv S i))
  let e : H.obj (ModuleCat.of L P) ≅ H.obj (colimit F) :=
    H.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportColimitEvalIso E r).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

end SerrePositivity.BhattScholze

end DeltaDivisionBoundedSupportTor

/-! ## 任意根族の全源Tor入力から元の実係数還元への比較 -/

@[expose] public noncomputable section DeltaRootBoundedSupportResidueDerived

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
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q" => L ⧸ I
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β
local notation "F" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E r
local notation "Res" => DeltaAdjoinDivisionResidue E (MvPolynomial.C d) r
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β) (ModuleCat.of P Res)

/-- 有界深さ図式のTor交換入力により、任意根族の実β拡大の高次Torは零。 -/
theorem Semiperfectoid.deltaRootBoundedSupportResidueEval_torVanishing
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    _root_.SerrePositivity.scalarExtensionTorVanishing β Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
    let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
    let : Subsingleton (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
        D d b hpA v hv i (hpres i)
    have hz : IsZero (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      ModuleCat.isZero_of_subsingleton _
    have hH := (_root_.SerrePositivity.derivedModuleBaseChangeHomologyIso ψ (i + 1)).app Mβ
    have hzH := hH.isZero_iff.mpr hz
    have hzR := (ModuleCat.restrictScalars ψ).map_isZero hzH
    have hzT := ((_root_.SerrePositivity.derivedModuleBaseChangeTorIso ψ (i + 1)).app Mβ).isZero_iff.mp hzR
    exact ((_root_.SerrePositivity.torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

/-- 同じ実β導来拡大は、既存raw残余商の次数零対象と標準augmentationで比較される。 -/
def Semiperfectoid.deltaRootBoundedSupportResidueDerivedIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange β).obj (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P Res) := by
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
  letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceResidueTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  letI : Module L Q := Algebra.toModule
  let e := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceResidueTensorAlgEquiv E (MvPolynomial.C d) r).toLinearEquiv
  exact _root_.SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentationIso β Mψ
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportResidueEval_torVanishing D d b hpA v hv hpres) ≪≫
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 比較の順射は、元の標準導来augmentationと通常raw残余比較の合成そのもの。 -/
theorem Semiperfectoid.deltaRootBoundedSupportResidueDerivedIso_hom
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceResidueTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L Q := Algebra.toModule
    let e := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (_root_.SerrePositivity.BhattScholze.deltaDivisionSourceResidueTensorAlgEquiv E (MvPolynomial.C d) r).toLinearEquiv
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportResidueDerivedIso D d b hpA v hv hpres).hom.hom =
      (_root_.SerrePositivity.boundedAboveDerivedBaseChangeModuleAugmentation β).app Mψ ≫
        (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

/-- 元の任意根族の実三因子係数還元は、同じraw残余商のsingleと標準同型。 -/
def Semiperfectoid.deltaRootBoundedSupportCoefficientResidueIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientReduced D d b ≅ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceResidueAssociatorReductionIso E (MvPolynomial.C d) r
  let e₂ := (_root_.SerrePositivity.boundedAboveDerivedBaseChangeTensorIso β
    (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (_root_.SerrePositivity.boundedAboveDerivedRestrictScalars β).mapIso
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportResidueDerivedIso D d b hpA v hv hpres)
  let e₄ : (_root_.SerrePositivity.boundedAboveDerivedRestrictScalars β).obj
      (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P Res)) ≅
        _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((_root_.SerrePositivity.derivedRestrictScalarsSingleIso β 0).app (ModuleCat.of P Res))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 同じ実三因子係数還元のH0は、βによる源作用を持つraw残余商と同型。 -/
def Semiperfectoid.deltaRootBoundedSupportCoefficientResidueH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    ((DerivedCategory.homologyFunctor (ModuleCat L) 0).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientReduced D d b).obj) ≅ MRes :=
  ((DerivedCategory.homologyFunctor (ModuleCat L) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientResidueIso D d b hpA v hv hpres))) ≪≫
        (_root_.SerrePositivity.realizedSingleH0Iso L).app MRes

/-- 同じ実三因子係数還元は、非零次数のホモロジーがすべて零。 -/
theorem Semiperfectoid.deltaRootBoundedSupportCoefficientResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientReduced D d b).obj) :=
  (_root_.SerrePositivity.derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientResidueIso D d b hpA v hv hpres)))

end SerrePositivity.BhattScholze

end DeltaRootBoundedSupportResidueDerived

/-! ## 任意根族の実商還元の純粋性とH0忠実平坦性

有界深さ有限部分族図式のTor交換を明示入力とする。
-/

@[expose] public noncomputable section DeltaRootBoundedSupportQuotientFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "k₀" => Ideal.span {(p : A), d}
local notation "κ₀" => Ideal.Quotient.mk k₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)

/-- 実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。 -/
def Semiperfectoid.deltaRootBoundedSupportQuotientDerivedRestrictedH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj) ≅ MRes :=
  ((_root_.SerrePositivity.derivedRestrictScalarsHomologyIso q₀ 0).app
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientDerivedRestrictionIso D d b)) ≪≫
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientResidueH0Iso
      D d b hpA v hv hpres

/-- 任意根族について、明示したTor交換入力の下で、実商環上の還元そのものの非零次数ホモロジーが消える。 -/
theorem Semiperfectoid.deltaRootBoundedSupportQuotientDerived_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj) := by
  have hz := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientResidue_homology_isZero
    D d b hpA v hv hpres i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientDerivedRestrictionIso D d b)))
  have hr := (_root_.SerrePositivity.derivedRestrictScalarsHomologyIso q₀ i).app
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。 -/
def Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedRestrictedH0Iso
    D d b hpA v hv hpres ≪≫ (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueRestrictionIso D d b).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- 任意根族について、明示したTor交換入力の下で、実導来商還元のH0は元のA/(p,d)上忠実平坦。 -/
theorem Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0_faithfullyFlat
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj)) := by
  have hpP : Function.Injective (fun x : P₀ => (p : P₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
  have hpL : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
  have hg := _root_.SerrePositivity.witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL
  let := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionResidueBaseAlgebra D d b hpP hpL hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj
  let M := (ModuleCat.restrictScalars
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0Iso D d b hpA v hv hpres
  let e : M ≃ₗ[A ⧸ k₀] Res₀ :=
    { toFun := eQ.hom.hom
      invFun := eQ.inv.hom
      left_inv := fun x => congrArg (fun f => f.hom x) eQ.hom_inv_id
      right_inv := fun x => congrArg (fun f => f.hom x) eQ.inv_hom_id
      map_add' := eQ.hom.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        change H at x
        have h := eQ.hom.hom.map_smul
          (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) x
        change eQ.hom.hom ((_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b
            (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) * eQ.hom.hom x at h
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap_mk,
          _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap_mk, _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEval_C] at h
        change eQ.hom.hom ((_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          _root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionResidueBaseMap D d b hpP hpL hg v hv (κ₀ a) * eQ.hom.hom x
        rw [_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap_mk,
          _root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionResidueBaseMap_mk]
        exact h }
  have := _root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionResidue_moduleFaithfullyFlat D d b hpP hpL hg v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e

local notation "X₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b

/-- 任意根族の実商還元は、標準t構造の非負部分に属する。 -/
theorem Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isGE_zero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_homology_isZero
    D d b hpA v hv hpres i (by omega)

/-- 同じ入力の下で標準t構造の非正部分にも属する。 -/
theorem Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isLE_zero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_homology_isZero
    D d b hpA v hv hpres i (by omega)

/-- 実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。 -/
def Semiperfectoid.deltaRootBoundedSupportQuotientDerivedSingleIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isGE_zero D d b hpA v hv hpres
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isLE_zero D d b hpA v hv hpres
  exact ObjectProperty.isoMk _ (_root_.SerrePositivity.normalizedPureHomologyIso (X₀).obj 0) ≪≫
    _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.mapIso
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0Iso D d b hpA v hv hpres)

/-- この導来同型のH0は、前工程で構成した具体的な商環線形同型そのもの。 -/
theorem Semiperfectoid.deltaRootBoundedSupportQuotientDerivedSingleIso_homologyZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedSingleIso
          D d b hpA v hv hpres).hom.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.app
        (ModuleCat.of Q₀ Res₀) =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0Iso D d b hpA v hv hpres).hom := by
  let := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isGE_zero D d b hpA v hv hpres
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerived_isLE_zero D d b hpA v hv hpres
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0Iso D d b hpA v hv hpres
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q₀) 0).hom.naturality
    e.hom
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
      ((DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _ at hn
  change (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).map
    ((_root_.SerrePositivity.normalizedPureHomologyIso (X₀).obj 0).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat Q₀) 0).map e.hom) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    _root_.SerrePositivity.normalizedPureHomologyIso_homology, Category.id_comp]
  rfl

end SerrePositivity.BhattScholze

end DeltaRootBoundedSupportQuotientFlat

/-! ## 元の係数環上の実(p,d)還元とraw残余商

任意根族（明示したTor交換入力の下）の実源商での比較を元の係数環へ渡す。一般Koszul還元や完備化後CFFは含まない。
-/

@[expose] public noncomputable section DeltaRootBoundedSupportPDResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)) (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b)
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 元のA上の実根添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。 -/
def Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceCoefficientPDReductionIso d D b ≪≫
    (_root_.SerrePositivity.boundedAboveDerivedRestrictScalars κ₀).mapIso
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedSingleIso D d b hpA v hv hpres) ≪≫
    ObjectProperty.isoMk _ ((_root_.SerrePositivity.derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。 -/
def Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres)) ≪≫
    (_root_.SerrePositivity.realizedSingleH0Iso R₀).app MRes

/-- 元のA上の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (_root_.SerrePositivity.derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres)))

/-- 元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。 -/
theorem Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueH0_faithfullyFlat
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceCoefficientPDReductionIso d D b)) ≪≫
    (_root_.SerrePositivity.derivedRestrictScalarsHomologyIso κ₀ 0).app (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceQuotientDerived D d b).obj
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportQuotientDerivedH0_faithfullyFlat
    D d b hpA v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootBoundedSupportPDResidue

/-! ## 実根添加対象の逐次主元完備化後の(p,d)還元

既存の二つの主元完備化を逐次適用した具体的対象を扱う。
原典の(p,d)完備化・環H0候補との比較や離散性は別工程である。
-/

@[expose] public noncomputable section DeltaRootBoundedSupportIteratedResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 任意根族（明示したTor交換入力の下）について、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。 -/
def Semiperfectoid.deltaRootBoundedSupportIteratedPDResidueIso
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b) ≅
      _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceIteratedPDReductionIso D d b hpA hd ≪≫
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres

/-- raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。 -/
theorem Semiperfectoid.deltaRootBoundedSupportIteratedPDResidueIso_unit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportIteratedPDResidueIso D d b hpA hd v hv hpres).hom =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres).hom := by
  let := (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportIteratedPDResidueIso, Iso.trans_hom]
  rw [← Category.assoc, _root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem Semiperfectoid.deltaRootBoundedSupportIteratedPDResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b)).obj) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidue_homology_isZero
    D d b hpA v hv hpres i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceIteratedPDReductionIso D d b hpA hd)))

/-- 逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。 -/
theorem Semiperfectoid.deltaRootBoundedSupportIteratedPDResidueH0_faithfullyFlat
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((_root_.SerrePositivity.boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceIteratedPDReductionIso D d b hpA hd))
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportCoefficientPDResidueH0_faithfullyFlat
    D d b hpA v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaRootBoundedSupportIteratedResidue

/-! ## 任意根族の標準図式に対する無条件のTor交換 -/

@[expose] public noncomputable section DeltaRootBoundedSupportTorInputs

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
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q" => L ⧸ I
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β
local notation "F" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionBoundedSupportModuleDiagram E r
local notation "Res" => DeltaAdjoinDivisionResidue E (MvPolynomial.C d) r
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β) (ModuleCat.of P Res)

/-- 共通G7-Finsetを元の有界深さ図式へ適用したTor交換。 -/
theorem Semiperfectoid.deltaRootBoundedSupport_preservesColimit :
    ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)) := by
  intro i
  let := _root_.SerrePositivity.torAlg_preservesFinsetColimits (σ × ℕ) ψ (i + 1)
  infer_instance

/-- 任意根族の全評価源の正次数Tor消滅。余極限交換の追加仮定は不要。 -/
theorem Semiperfectoid.deltaRootEvaluation_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    D d b hpA v hv i (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupport_preservesColimit D d b i)

/-- 元の実β評価の高次Tor消滅を、具体的係数加群とともに供給する。 -/
theorem Semiperfectoid.deltaRootBoundedSupportResidueEval_torVanishing_unconditional
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    _root_.SerrePositivity.scalarExtensionTorVanishing β Mψ := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupportResidueEval_torVanishing D d b hpA v hv
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootBoundedSupport_preservesColimit D d b)

end SerrePositivity.BhattScholze

end DeltaRootBoundedSupportTorInputs

/-! ## 具体的根添加候補の正則生成元冪商とp導来完備性

A/(dⁿ)への実導来基底変更を、元のAへ係数制限して扱う。
商環上の完備性との係数環比較や離散性は別工程である。
-/

@[expose] public noncomputable section DeltaRootSourceGeneratorPowerReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "X₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b

/-- 正則dの実冪商への基底変更を制限すると、候補の実dⁿ Koszul錐になる。 -/
def Semiperfectoid.deltaRootSourceGeneratorPowerReductionKoszulIso (hd : IsSMulRegular A d) (n : ℕ) :
    ((_root_.SerrePositivity.boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (_root_.SerrePositivity.DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  _root_.SerrePositivity.restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X₀

/-- 正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。 -/
theorem Semiperfectoid.deltaRootSourceGeneratorPowerReduction_isComplete_p
    (hd : IsSMulRegular A d) (n : ℕ) :
    _root_.SerrePositivity.DerivedCompletion.IsComplete A (p : A)
      (((_root_.SerrePositivity.boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        ((_root_.SerrePositivity.boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj) := by
  let K := DerivedCategory.Q.objPreimage (X₀).obj
  let eK : DerivedCategory.Q.obj K ≅ (X₀).obj := DerivedCategory.Q.objObjPreimageIso (X₀).obj
  have hK : _root_.SerrePositivity.DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    _root_.SerrePositivity.DerivedCompletion.isComplete_of_iso A (p : A) eK.symm
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSourceIteratedPDCompletion_isComplete_p D d b)
  have hC := _root_.SerrePositivity.DerivedCompletion.isComplete_Q_mappingCone A (p : A) (_root_.SerrePositivity.smulId (d ^ n) K) hK hK
  let e := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReductionKoszulIso D d b hd n ≪≫
    (_root_.SerrePositivity.DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
      (_root_.SerrePositivity.DerivedCompletion.derivedScalarConeComparison A (d ^ n)).app K
  exact _root_.SerrePositivity.DerivedCompletion.isComplete_of_iso A (p : A) e.symm hC

local notation "Y₀" =>
  CategoryTheory.Functor.obj (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A))
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b)
local notation "U₀" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 最後のd完備化単位は、各生成元冪商での実還元後に同型になる。 -/
theorem Semiperfectoid.deltaRootSourceGeneratorPowerReduction_unit_isIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsIso ((_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
      ((U₀).app Y₀)) :=
  _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A d hd n Y₀

/-- p完備化済み対象と逐次対象の冪商還元を、標準d完備化単位で比較する。 -/
def Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj Y₀ ≅
      (_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀ := by
  have := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReduction_unit_isIso D d b hd n
  exact asIso ((_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
    ((U₀).app Y₀))

/-- 冪商還元の比較逆射は、還元した標準d完備化単位の左逆である。 -/
theorem Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso_unit
    (hd : IsSMulRegular A d) (n : ℕ) :
    (_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
        ((U₀).app Y₀) ≫
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).inv = 𝟙 _ :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).hom_inv_id

/-- 冪商の完備化比較は、実Koszul比較の下で標準単位の錐上の射に一致する。 -/
theorem Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso_koszul
    (hd : IsSMulRegular A d) (n : ℕ) :
    ((_root_.SerrePositivity.boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).map
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReductionCompletionIso D d b hd n).hom).hom ≫
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReductionKoszulIso D d b hd n).hom =
    (_root_.SerrePositivity.restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) Y₀).hom ≫
      (_root_.SerrePositivity.DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).map (((U₀).app Y₀).hom) :=
  _root_.SerrePositivity.restrictedDerivedQuotientKoszulIso_naturality (d ^ n) (hd.pow n) ((U₀).app Y₀)

end SerrePositivity.BhattScholze

end DeltaRootSourceGeneratorPowerReduction

/-! ## 係数制限と完備化の比較による生成元冪商上のp導来完備性

既証の係数制限後の完備性を、元の標準単位の図式と同型反映で商環へ戻す。
-/

@[expose] public noncomputable section DeltaRootSourceGeneratorPowerComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 正則生成元の任意冪商への実還元は、その商環上でp導来完備。n=0も含む。 -/
theorem Semiperfectoid.deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((_root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b)).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((_root_.SerrePositivity.boundedAboveDerivedBaseChange q).obj
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b)).obj
  let F := _root_.SerrePositivity.derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceGeneratorPowerReduction_isComplete_p D d b hd n
  have hunitR : IsIso ((derivedComplexCompletionUnit A (p : A)).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A (p : A) (F.obj Y) hR
  let e := derivedRestrictionCompletionIso q (p : A)
  have hc : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y) ≫
      e.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q (p : A))).app Y) :=
    isIso_of_reflects_iso _ F
  have hcomplete := (isComplete_iff_derivedComplexCompletionUnit_isIso T (q (p : A)) Y).mpr hS
  simpa only [map_natCast] using hcomplete

end SerrePositivity.BhattScholze

end DeltaRootSourceGeneratorPowerComplete

/-! ## 完全δ環のrank-one元の具体的互換p冪根列 -/

@[expose] public noncomputable section PerfectDeltaRankOneRoots

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環で逆Frobeniusをn回適用した指定元の具体的な根候補。 -/
def Semiperfectoid.perfectDeltaRankOneRoot (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (x : A) (n : ℕ) : A :=
  ((D.frobeniusEquiv hD).symm : A → A)^[n] x

/-- 根列の零段は指定元そのもの。 -/
@[simp] theorem Semiperfectoid.perfectDeltaRankOneRoot_zero (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (x : A) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x 0 = x := rfl

/-- 根列の次段は前段への逆Frobeniusの適用。 -/
theorem Semiperfectoid.perfectDeltaRankOneRoot_succ (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x (n + 1) =
      (D.frobeniusEquiv hD).symm (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n) :=
  Function.iterate_succ_apply' _ _ _

/-- 指定元のδ値が零なら根列の各段のδ値も零。 -/
theorem Semiperfectoid.perfectDeltaRankOneRoot_delta (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (hx : D.delta x = 0) (n : ℕ) :
    D.delta (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n) = 0 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot_succ]
      have h := D.frobeniusEquiv_symm_isDeltaHom hD (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n)
      rw [ih, map_zero] at h
      exact h.symm

/-- rank-one元の次の根のp乗は前の根に一致する。 -/
theorem Semiperfectoid.perfectDeltaRankOneRoot_pow (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect)
    (x : A) (hx : D.delta x = 0) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x (n + 1) ^ p = _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n := by
  have h := (D.frobeniusEquiv hD).apply_symm_apply (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n)
  change D.frobeniusLift ((D.frobeniusEquiv hD).symm (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n)) = _ at h
  rw [← _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot_succ] at h
  rw [D.frobeniusLift_apply, _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot_delta D hD x hx, mul_zero, add_zero] at h
  exact h

/-- 任意通常環射で根列の像を取っても、同じ互換p冪根条件を満たす。 -/
theorem Semiperfectoid.perfectDeltaRankOneRoot_map_pow {T : Type v} [CommRing T]
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p A) (hD : D.IsPerfect) (x : A) (hx : D.delta x = 0)
    (q : A →+* T) (n : ℕ) :
    q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x (n + 1)) ^ p = q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot D hD x n) := by
  rw [← map_pow, _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot_pow D hD x hx]

end SerrePositivity.BhattScholze

end PerfectDeltaRankOneRoots

/-! ## 根δ除算包の通常商における指定元の互換p冪根族 -/

@[expose] public noncomputable section DeltaRootAdjoinCompatibleRoots

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
variable {C : Type w} [CommRing C] {T : Type z} [CommRing T]
variable (E : DeltaStructure p C) (hE : E.IsPerfect)
variable (f : _root_.SerrePositivity.BhattScholze.Andre.DeltaRootAdjoinDivision D d b →+* C) (q : C →+* T)

/-- raw根変数のδ値零は、任意の指定δ射で保存される。 -/
theorem Semiperfectoid.deltaRootAdjoinDivisionVariable_map_delta
    (hf : (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)).IsDeltaHom E f) (s : σ) :
    E.delta (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)) = 0 := by
  have h := hf (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable_delta, map_zero] at h
  exact h.symm

/-- 指定元の像を零段とし、根変数への逆Frobenius列の通常商像を続ける具体的族。 -/
def Semiperfectoid.deltaRootAdjoinCompatibleRoots (s : σ) : ℕ → T
  | 0 => q (f (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s))))
  | n + 1 => q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot E hE (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)) n)

/-- 根族の零段は指定元の元の係数射による像。 -/
theorem Semiperfectoid.deltaRootAdjoinCompatibleRoots_zero (s : σ) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots D d b E hE f q s 0 =
      q (f (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b) (MvPolynomial.C (b s)))) := rfl

/-- 零段以降の根族は、根変数への逆Frobenius列の通常商像そのもの。 -/
theorem Semiperfectoid.deltaRootAdjoinCompatibleRoots_succ (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots D d b E hE f q s (n + 1) =
      q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot E hE (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)) n) := rfl

/-- dの像を消す通常商において、指定元の像から始まる根族は互換p冪根条件を満たす。 -/
theorem Semiperfectoid.deltaRootAdjoinCompatibleRoots_pow
    (hf : (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)).IsDeltaHom E f)
    (hd : q (f (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b) (MvPolynomial.C d))) = 0) (s : σ) (n : ℕ) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots D d b E hE f q s (n + 1) ^ p =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots D d b E hE f q s n := by
  cases n with
  | zero =>
      change q (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)) ^ p = _
      exact _root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable_map_pow D d b (q.comp f) hd s
  | succ n =>
      change q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot E hE (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s))
        (n + 1)) ^ p =
          q (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot E hE (f (_root_.SerrePositivity.BhattScholze.Andre.deltaRootAdjoinDivisionVariable D d b s)) n)
      exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaRankOneRoot_map_pow E hE _
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinDivisionVariable_map_delta D d b E f hf s) q n

end SerrePositivity.BhattScholze

end DeltaRootAdjoinCompatibleRoots

/-! ## 根δ除算包からの具体的なperfectoid候補

既存のp進完備δ完全化と実PD完備化を使用する。標準基底射の完全忠実平坦性は
この構成からは結論しない。商のpねじれ・零環を許す。
-/

@[expose] public noncomputable section DeltaRootPerfectoidCandidate

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 根δ除算包の既存p進完備δ完全化。 -/
abbrev Semiperfectoid.DeltaRootPCompletion :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)

/-- p進完備δ完全化における選択元dの標準像。 -/
def Semiperfectoid.deltaRootPCompletionGenerator : _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b) (MvPolynomial.C d)

/-- 根候補の実導来(p,d)完備化のH⁰。 -/
abbrev Semiperfectoid.DeltaRootPrismCarrier :=
  PDCompletionH0 (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)

/-- 実完備化に既存の可換環構造を使用する。 -/
@[instance_reducible] def Semiperfectoid.deltaRootPrismCommRing : CommRing (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) :=
  pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)

/-- distinguished dを持つ基底からの具体的な完全prism候補。 -/
def Semiperfectoid.deltaRootPrism (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.OrientedPrism p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect _ _ _) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom _ _ _).map_isDistinguished
      ((_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd))

/-- 候補prismのδ構造は完全。 -/
theorem Semiperfectoid.deltaRootPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).deltaStructure.IsPerfect := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.deltaPDCompletionStructure_isPerfect
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect _ _ _) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)

/-- raw根δ除算包から実完備化への標準射。 -/
def Semiperfectoid.deltaRootPrismRawMap :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Andre.DeltaRootAdjoinDivision D d b →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b :=
  (pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)).comp
    (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure
      (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)))

/-- 標準raw射は既存の二つのδ射の合成。 -/
theorem Semiperfectoid.deltaRootPrismRawMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionStructure (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)).IsDeltaHom
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).deltaStructure (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom _ _).comp (_root_.SerrePositivity.BhattScholze.pCompletedDeltaPerfectionMap_isDeltaHom _)

/-- 完全prism候補の標準商を実際のperfectoid候補とする。 -/
abbrev Semiperfectoid.DeltaRootPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b ⧸ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal

/-- 候補の標準商は整perfectoid。標準基底射の平坦性は別の主張。 -/
theorem Semiperfectoid.deltaRootPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.IsIntegralPerfectoid (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd) p := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).quotient_isIntegralPerfectoid
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism_isPerfect D d b hd)

/-- 基底δ環から候補の通常商への具体的係数射。 -/
def Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    A →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal).comp
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b).comp
      ((_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)).comp MvPolynomial.C))

/-- 選択元dの係数像は標準商で零になる。 -/
theorem Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap_d (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd d = 0 := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  change Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).generator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 元の通常商A/(d)からperfectoid候補への具体的な基底射。 -/
def Semiperfectoid.deltaRootPerfectoidCandidateBaseMap (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    A ⧸ Ideal.span {d} →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  have hker : Ideal.span {d} ≤
      RingHom.ker (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd) :=
    Ideal.span_le.mpr (by
      intro x hx
      have hxd : x = d := Set.mem_singleton_iff.mp hx
      subst x
      exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap_d D d b hd)
  exact Ideal.Quotient.lift _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd)
    (fun x hx ↦ hker hx)

/-- 基底射は各商代表の標準係数像と一致する。 -/
theorem Semiperfectoid.deltaRootPerfectoidCandidateBaseMap_mk (hd : D.IsDistinguished d) (x : A) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateBaseMap D d b hd (Ideal.Quotient.mk _ x) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd x := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  simp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateBaseMap, Ideal.Quotient.lift_mk]

/-- perfectoid候補での具体的互換根族。 -/
def Semiperfectoid.deltaRootPerfectoidCandidateRoots (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    σ → ℕ → _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots D d b (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).deltaStructure
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism_isPerfect D d b hd) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b)
    (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal)

/-- 互換根族の零段は元の通常商からの基底射による指定元の像。 -/
theorem Semiperfectoid.deltaRootPerfectoidCandidateRoots_zero (hd : D.IsDistinguished d) (s : σ) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateRoots D d b hd s 0 =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateBaseMap D d b hd (Ideal.Quotient.mk _ (b s)) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateBaseMap_mk]
  rfl

/-- 候補内の根族はすべての段で互換p冪根条件を満たす。 -/
theorem Semiperfectoid.deltaRootPerfectoidCandidateRoots_pow (hd : D.IsDistinguished d) (s : σ) (n : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateRoots D d b hd s (n + 1) ^ p =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateRoots D d b hd s n := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  apply _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootAdjoinCompatibleRoots_pow
    D d b _ _ _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap_isDeltaHom D d b hd)
  change Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).generator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

end SerrePositivity.BhattScholze

end DeltaRootPerfectoidCandidate

/-! ## 根添加prism候補への基底射と標準商射

既存候補への具体的係数射をprism射に束ねる。平坦性は別工程である。
-/

@[expose] public noncomputable section DeltaRootPrismBaseMap

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (b : σ → A)

/-- 基底から既存の根添加prism候補の台環への具体的係数射。 -/
def Semiperfectoid.deltaRootPrismCoefficientMap :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    A →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b).comp
    ((_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure σ D) (MvPolynomial.C d)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b)).comp MvPolynomial.C)

/-- 候補への係数射は、既存の標準δ射を合成したδ射である。 -/
theorem Semiperfectoid.deltaRootPrismCoefficientMap_isDeltaHom (hd : D.IsDistinguished d) :
    let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    D.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).deltaStructure
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap_isDeltaHom D d b hd).comp
    ((_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap_isDeltaHom _ _ _).comp
      (_root_.SerrePositivity.BhattScholze.polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

/-- 係数射は基底のdを候補prismの選択生成元そのものへ送る。 -/
theorem Semiperfectoid.deltaRootPrismCoefficientMap_generator (hd : D.IsDistinguished d) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b d = (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).generator := rfl

/-- 基底の主イデアルの像は、候補prismのイデアル全体に一致する。 -/
theorem Semiperfectoid.deltaRootPrismCoefficientMap_ideal (hd : D.IsDistinguished d) :
    let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (Ideal.span {d}).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b) =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  change (Ideal.span {d}).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b) =
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal
  rw [Ideal.map_span, Set.image_singleton, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap_generator D d b hd]
  rfl

/-- distinguished生成元を持つ元のprismから、既存の根添加prism候補への標準射。 -/
def Semiperfectoid.deltaRootPrismBaseHom (P : _root_.SerrePositivity.BhattScholze.OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (b : σ → A) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing P.deltaStructure P.generator b
    _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism P.deltaStructure P.generator b hd) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing P.deltaStructure P.generator b
  refine ⟨_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap P.deltaStructure P.generator b,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap_isDeltaHom P.deltaStructure P.generator b hd, ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  change (Ideal.span {P.generator}).map _ ≤ _
  exact (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap_ideal P.deltaStructure P.generator b hd).le

/-- 標準prism射の誘導商射は、既存perfectoid候補への基底射に一致する。 -/
theorem Semiperfectoid.deltaRootPrismBaseHom_quotientMap (P : _root_.SerrePositivity.BhattScholze.OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (b : σ → A) :
    let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing P.deltaStructure P.generator b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismBaseHom P hd b).quotientMap =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateBaseMap P.deltaStructure P.generator b hd := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing P.deltaStructure P.generator b
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end SerrePositivity.BhattScholze

end DeltaRootPrismBaseMap

/-! ## 既存根添加候補と直接PD完備化の標準環・商比較 -/

@[expose] public noncomputable section DeltaRootDirectPDCompletionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "ι" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "z" => ι (MvPolynomial.C d)
local notation "C" => DeltaPerfection F
local notation "x" => deltaPerfectionOf F 0 z
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "r₀" => RingHom.comp s (deltaPerfectionOf F 0)

/-- 根raw環のδ完全化の直接PD完備化は、既存prism台環候補と標準環同型。 -/
def Semiperfectoid.deltaRootDirectPDCompletionEquiv :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    H ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv F z

/-- 環比較は、元の根raw環からの両標準射を保つ。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_raw :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b).toRingHom.comp r₀ =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.deltaPerfectionPDCompletionEquiv_spec F z).2.2

/-- 環比較は、元Aの具体的標準係数射を保つ。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_coefficient :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b).toRingHom.comp
        ((r₀).comp ((ι).comp MvPolynomial.C)) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  rw [← RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_raw]
  rfl

/-- 直接PD完備化の選択元像は、既存候補の同じ選択元像へ移る。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionEquiv_generator :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b (s x) =
      pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_raw D d b) z

/-- 生成元の標準主イデアル商は、既存の実perfectoid候補と環同型。 -/
def Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (H ⧸ Ideal.span {s x}) ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b) (by
    rw [Ideal.map_span, Set.image_singleton]
    symm
    change Ideal.span (Set.singleton (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b (s x))) =
      Ideal.span (Set.singleton (pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)))
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv_generator])

/-- 商比較は、代表元に具体的な標準環同型を適用する。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    ∀ h : H, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv D d b hd (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b h) := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  intro h
  rfl

/-- 商環比較は、元Aから既存perfectoid候補への同じ具体的係数射を保つ。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv D d b hd).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {s x})).comp
          ((r₀).comp ((ι).comp MvPolynomial.C))) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b
      (((r₀).comp ((ι).comp MvPolynomial.C)) a)) =
    Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b a)
  exact congrArg (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal)
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_coefficient D d b) a)

/-- 直接PD完備化の同じ具体的生成元商も、既存候補から整perfectoid性を受け取る。 -/
theorem Semiperfectoid.deltaRootDirectPDCompletionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing C p x
    _root_.SerrePositivity.IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionQuotientEquiv D d b hd).symm
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd)

end SerrePositivity.BhattScholze

end DeltaRootDirectPDCompletionComparison

/-! ## PD完備化済み根δ環のδ完全化と既存候補の標準比較 -/

@[expose] public noncomputable section DeltaRootPDCompletedPerfectionComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "ι" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "z" => ι (MvPolynomial.C d)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "S" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "r₀" => RingHom.comp (RingHom.comp s (deltaPerfectionOf G 0)) v

/-- PD完備化済み根δ環のδ完全化の実PD完備化は、既存prism台環候補と標準環同型。 -/
def Semiperfectoid.deltaRootPDCompletedPerfectionEquiv :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    H ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPrismCarrier D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact (_root_.SerrePositivity.BhattScholze.deltaPDCompletionPerfectionEquiv F z).symm.trans
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b)

/-- 環比較は、元の根raw環からの両標準射を保つ。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_comp_raw :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b).toRingHom.comp r₀ =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  have h : (_root_.SerrePositivity.BhattScholze.deltaPDCompletionPerfectionEquiv F z).symm (r₀ a) =
      pdCompletionUnit (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
        (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 a) :=
    RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.deltaPDCompletionPerfectionInverse_spec F z).2 a
  change _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv D d b
    ((_root_.SerrePositivity.BhattScholze.deltaPDCompletionPerfectionEquiv F z).symm (r₀ a)) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismRawMap D d b a
  rw [h]
  exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootDirectPDCompletionEquiv_comp_raw D d b) a

/-- 環比較は、元Aの具体的標準係数射を保つ。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_comp_coefficient :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b).toRingHom.comp
        ((r₀).comp ((ι).comp MvPolynomial.C)) = _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  rw [← RingHom.comp_assoc, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_comp_raw]
  rfl

/-- PD先行構成の選択元像は、既存候補の同じ選択元像へ移る。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_generator :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b (s x) =
      pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_comp_raw D d b) z

/-- 生成元の標準主イデアル商は、既存の実perfectoid候補と環同型。 -/
def Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (H ⧸ Ideal.span {s x}) ≃+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPerfectoidCandidate D d b hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b) (by
    rw [Ideal.map_span, Set.image_singleton]
    symm
    change Ideal.span (Set.singleton (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b (s x))) =
      Ideal.span (Set.singleton (pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootPCompletion D d b) p
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPCompletionGenerator D d b)))
    rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_generator])

/-- 商比較は、代表元に具体的な標準環同型を適用する。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    ∀ h : H, _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv D d b hd (Ideal.Quotient.mk _ h) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b h) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  intro h
  rfl

/-- 商環比較は、元Aから既存perfectoid候補への同じ具体的係数射を保つ。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv D d b hd).toRingHom.comp
        ((Ideal.Quotient.mk (Ideal.span {s x})).comp
          ((r₀).comp ((ι).comp MvPolynomial.C))) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidateCoefficientMap D d b hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv D d b
      (((r₀).comp ((ι).comp MvPolynomial.C)) a)) =
    Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCoefficientMap D d b a)
  exact congrArg (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrism D d b hd).ideal)
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionEquiv_comp_coefficient D d b) a)

/-- PD先行構成の同じ具体的生成元商も、既存候補から整perfectoid性を受け取る。 -/
theorem Semiperfectoid.deltaRootPDCompletedPerfectionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    _root_.SerrePositivity.IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.DeltaPerfection F) p (_root_.SerrePositivity.BhattScholze.deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPrismCommRing D d b
  exact _root_.SerrePositivity.BhattScholze.isIntegralPerfectoid_of_ringEquiv p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPDCompletedPerfectionQuotientEquiv D d b hd).symm
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootPerfectoidCandidate_isIntegralPerfectoid D d b hd)

end SerrePositivity.BhattScholze

end DeltaRootPDCompletedPerfectionComparison

/-! ## 元の実導来源からraw r/d包とその実完備化への比較射 -/

@[expose] public noncomputable section DeltaRootSourceRawComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => _root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- raw包に、評価βを経由する元の実源L作用を明示した加群対象。 -/
def Semiperfectoid.DeltaRootSourceRawModule : ModuleCat.{u} L := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 通常二因子テンソルとraw包は、元の実源L上で線形同型。 -/
def Semiperfectoid.deltaRootSourceOrdinaryTensorRawIso :
    (tensorLeft Mβ).obj Mα ≅ _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b := by
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceEvaluationAlgebra E r
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r) (by
      intro x
      change _root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r
        (β x ⊗ₜ[L] 1) = (_root_.SerrePositivity.BhattScholze.deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (β x)
      rw [_root_.SerrePositivity.BhattScholze.deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 800000 in
-- Match the actual two scalar modules with the original bounded derived tensor object.
/-- 元の実導来二因子源から、raw次数零対象への標準augmentation。 -/
def Semiperfectoid.deltaRootSourceRawAugmentation :
    X ⟶ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b) := by
  let f : X ⟶ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj ((tensorLeft Mβ).obj Mα) :=
    ObjectProperty.homMk ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα)
  exact f ≫ _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceOrdinaryTensorRawIso D d b).hom

set_option maxHeartbeats 800000 in
-- Match the actual two scalar modules with the original bounded derived tensor object.
/-- 元の実導来二因子源のH0と実源作用付きraw包の比較。 -/
def Semiperfectoid.deltaRootSourceRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b :=
  (_root_.SerrePositivity.boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceOrdinaryTensorRawIso D d b

/-- raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。 -/
theorem Semiperfectoid.deltaRootSourceRawAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawAugmentation D d b).hom) := by
  have := _root_.SerrePositivity.derivedTensorAugmentation_h0_isIso (R := L) Mβ Mα
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
    (((_root_.SerrePositivity.boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα) ≫
      (DerivedCategory.singleFunctor (ModuleCat L) 0).map
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceOrdinaryTensorRawIso D d b).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 元のAへ係数制限したraw次数零対象。 -/
abbrev Semiperfectoid.DeltaRootSourceRawCoefficientObject :=
  (_root_.SerrePositivity.boundedAboveDerivedRestrictScalars C₀).obj
    (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b))

set_option maxHeartbeats 800000 in
-- Compare the original tensor object through coefficient restriction and actual homology.
/-- 元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。 -/
def Semiperfectoid.deltaRootSourceRawCoefficientH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b).obj ≅
      (ModuleCat.restrictScalars C₀).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b) :=
  (_root_.SerrePositivity.derivedRestrictScalarsHomologyIso C₀ 0).app (X).obj ≪≫
    (ModuleCat.restrictScalars C₀).mapIso (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawH0Iso D d b)

/-- 元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。 -/
def Semiperfectoid.deltaRootSourceRawCoefficientAugmentation :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b ⟶ _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b :=
  (_root_.SerrePositivity.boundedAboveDerivedRestrictScalars C₀).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawAugmentation D d b)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。 -/
abbrev Semiperfectoid.DeltaRootSourceRawIteratedCompletion :=
  (Cd).obj ((Cp).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b))

/-- 元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。 -/
def Semiperfectoid.deltaRootSourceRawIteratedComparison :
    _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b ⟶ _root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawIteratedCompletion D d b :=
  (Cd).map ((Cp).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b))

/-- 完備化後の比較射は、元のp,d合成標準単位と可換。 -/
theorem Semiperfectoid.deltaRootSourceRawIteratedComparison_unit :
    ((Up).app (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b) ≫
      (Ud).app ((Cp).obj (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b))) ≫
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedComparison D d b =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b ≫
        ((Up).app (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b) ≫
          (Ud).app ((Cp).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b))) := by
  let f := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b
  have hp := (Up).naturality f
  have hd := (Ud).naturality ((Cp).map f)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedComparison]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze

end DeltaRootSourceRawComparison

/-! ## 元の実根添加源の非正性と同じ係数制限augmentationのH0同型 -/

@[expose] public noncomputable section DeltaRootSourceNonpositive

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
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- Retain the original scalar actions while comparing explicit nonpositive projective tensor models.
/-- 同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。 -/
theorem Semiperfectoid.deltaRootSourceCoefficient_isLE_zero :
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b).obj.IsLE 0 := by
  let Pβ := _root_.SerrePositivity.projectiveResolutionDerivedModel (projectiveResolution Mβ)
  let Pα := _root_.SerrePositivity.projectiveResolutionDerivedModel (projectiveResolution Mα)
  let K := _root_.SerrePositivity.cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat A) ℤ :=
    ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using _root_.SerrePositivity.cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars C₀).obj (K.X i))
    exact (ModuleCat.restrictScalars C₀).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b).obj ≅ DerivedCategory.Q.obj KR :=
    (_root_.SerrePositivity.derivedRestrictScalars C₀).mapIso
        (_root_.SerrePositivity.boundedAboveDerivedTensorModelIso
          (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mβ)
          (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Mα) Pβ Pα) ≪≫
      (_root_.SerrePositivity.derivedRestrictScalarsFactors C₀).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。 -/
theorem Semiperfectoid.deltaRootSourceCoefficient_homology_isZero_positive (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceCoefficientObject d D b).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceCoefficient_isLE_zero D d b) i hi

/-- 同じaugmentationの終域である係数制限raw singleも非正次数である。 -/
theorem Semiperfectoid.deltaRootSourceRawCoefficient_isLE_zero :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj.IsLE 0 := by
  let e : (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawCoefficientObject D d b).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b)) :=
    (_root_.SerrePositivity.derivedRestrictScalarsSingleIso C₀ 0).app (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawModule D d b)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。 -/
theorem Semiperfectoid.deltaRootSourceRawCoefficientAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b).hom) := by
  let f := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawAugmentation D d b).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := _root_.SerrePositivity.derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map f) :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawAugmentation_h0_isIso D d b
  have hn := e.hom.naturality f
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((_root_.SerrePositivity.derivedRestrictScalars C₀).map f) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((_root_.SerrePositivity.derivedRestrictScalars C₀).map f))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze

end DeltaRootSourceNonpositive

/-! ## 元の実根添加源の逐次完備化と同じaugmentationのH0比較 -/

@[expose] public noncomputable section DeltaRootSourceCompletionH0

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d

/-- 元の実係数源のp,d逐次実完備化も非正である。 -/
theorem Semiperfectoid.deltaRootSourceIteratedPDCompletion_isLE_zero :
    (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b).obj.IsLE 0 := by
  apply _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceCoefficient_isLE_zero D d b)

/-- raw係数対象の同じp,d逐次実完備化も非正である。 -/
theorem Semiperfectoid.deltaRootSourceRawIteratedCompletion_isLE_zero :
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawIteratedCompletion D d b).obj.IsLE 0 := by
  apply _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficient_isLE_zero D d b)

/-- 同じ元のaugmentationは、実p完備化後にもH0同型を誘導する。 -/
theorem Semiperfectoid.deltaRootSourceRawPComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((Cp).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b)).hom)) := by
  exact _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A (p : A)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceCoefficient_isLE_zero D d b)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficient_isLE_zero D d b)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation_h0_isIso D d b)

/-- 既存の標準逐次完備化比較射そのものがH0同型を誘導する。 -/
theorem Semiperfectoid.deltaRootSourceRawIteratedComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedComparison D d b).hom) := by
  exact _root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A d
    ((Cp).map (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficientAugmentation D d b))
    (_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceCoefficient_isLE_zero D d b))
    (_root_.SerrePositivity.DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawCoefficient_isLE_zero D d b))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawPComparison_h0_isIso D d b)

/-- 実逐次源のH0とrawの実逐次完備化のH0を、同じ標準比較射で同定する。 -/
def Semiperfectoid.deltaRootSourceRawIteratedH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.DeltaRootSourceRawIteratedCompletion D d b).obj := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedComparison_h0_isIso D d b
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.deltaRootSourceRawIteratedComparison D d b).hom)

end SerrePositivity.BhattScholze

end DeltaRootSourceCompletionH0

/-! ## 根付き生成族による全射商の全射性

核の全元の根は要求せず、核を生成する族の初項の根を使う。
これにより、根付き拡大の入力を元の核の生成族だけに制限できる。
-/

@[expose] public noncomputable section RootedPresentationSurjectivity

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C σ : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 核が根族の初項で生成される全射商の任意のperfectoid化は全射。
核の全元の根・生成族の有限性・商のp正則性・完備性は不要。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_rootedPresentation
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (hk : RingHom.ker q = _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ)
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  let e : R ⧸ _root_.SerrePositivity.BhattScholze.compatibleRootFamilyZeroIdeal ρ ≃+* S :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
  have hfe : _root_.SerrePositivity.IsPerfectoidization p (f.comp e.toRingHom) := hf.precomp_ringEquiv e
  have hs := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_compatibleRootFamily hR ρ hρ
    (f.comp e.toRingHom) hfe
  intro c
  obtain ⟨x, hx⟩ := hs c
  exact ⟨e x, hx⟩

end SerrePositivity.BhattScholze

end RootedPresentationSurjectivity

/-! ## 元の核の生成族の根だけを持つ拡大からの降下

底変換した核の全元の根や拡大の整代数的閉性を要求しない。
任意の元の核の生成族の像に根を供給する、必要な拡大データを明示する。
-/

@[expose] public noncomputable section RootedFamilyPerfectoidSurjectivityDescent

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped _root_.TensorProduct
variable {p : ℕ} [Fact p.Prime] {R S C T E σ : Type u}
variable [CommRing R] [CommRing S] [CommRing C] [CommRing T] [CommRing E]
variable [Algebra R S] [Algebra R C] [Algebra R T]

/-- 元の核の生成族の像が根を持てば、通常底変換したperfectoid化の合成射は全射。 -/
theorem Semiperfectoid.surjective_perfectoidizationTensorBaseChangeMap_of_rootedGeneratingFamily
    (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p) (hq : Function.Surjective (algebraMap R S))
    (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom)
    (F : C ⊗[R] T →+* E) (hF : _root_.SerrePositivity.IsPerfectoidization p F) :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap f F) := by
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_rootedPresentation hT
    (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom
    (Algebra.TensorProduct.includeRight_surjective T hq) ρ hρ
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.tensorBaseChangeKernel_eq_rootFamilyZeroIdeal hq a ha ρ hρ0)
    (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap f F)
    (_root_.SerrePositivity.BhattScholze.perfectoidizationTensorBaseChangeMap_isPerfectoidization p f hf F hF)

/-- 根付きp完全忠実平坦perfectoid拡大を、元の核の任意の生成族について供給すれば、
導来p完備な全射商の任意perfectoid化は全射。拡大の存在は入力として残る。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_rootedGeneratingFamilyBaseChange
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (hq : Function.Surjective (algebraMap R S))
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (a : σ → R) (ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a))
    (ρ : σ → ℕ → T) (hρ0 : ∀ s, ρ s 0 = algebraMap R T (a s))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →ₐ[R] C) (hf : _root_.SerrePositivity.IsPerfectoidization p f.toRingHom) : Function.Surjective f := by
  obtain ⟨E, hE, F, hF, hbij, _⟩ := _root_.SerrePositivity.BhattScholze.exists_perfectoidizationTensorBaseChange p hR hT f hf
  have hsurj := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_perfectoidizationTensorBaseChangeMap_of_rootedGeneratingFamily
    hT hq a ha ρ hρ0 hρ f hf F hF
  have hmod : Function.Surjective
      (_root_.SerrePositivity.modPMap p (Algebra.TensorProduct.map f (AlgHom.id R T)).toRingHom) := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hsurj (F c)
    refine ⟨Ideal.Quotient.mk _ x, hbij.injective ?_⟩
    change Ideal.Quotient.mk (Ideal.span {(p : E)})
      (F (Algebra.TensorProduct.map f (AlgHom.id R T) x)) =
        Ideal.Quotient.mk (Ideal.span {(p : E)}) (F c)
    exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : E)})) hx
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_residue_baseChange f hf hS hflat
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_principalResidueTensor_of_modP_tensorMap p R S T f hmod)

omit [Algebra R S] [Algebra R C] in
/-- 具体的な全射q:R→Sについて、元の核の各元の像にだけ両立する根を持つ
p完全忠実平坦perfectoid拡大があれば、任意perfectoid化f:S→Cは全射。 -/
theorem Semiperfectoid.surjective_of_isPerfectoidization_of_sourceKernelRoots
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (hT : _root_.SerrePositivity.IsIntegralPerfectoid T p)
    (q : R →+* S) (hq : Function.Surjective q)
    (hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (hflat : _root_.SerrePositivity.IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T)
    (ρ : RingHom.ker q → ℕ → T)
    (hρ0 : ∀ s, ρ s 0 = algebraMap R T (s : R))
    (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (f : S →+* C) (hf : _root_.SerrePositivity.IsPerfectoidization p f) : Function.Surjective f := by
  let : Algebra R S := q.toAlgebra
  let : Algebra R C := (f.comp q).toAlgebra
  let ff : S →ₐ[R] C := { f with commutes' := fun _ ↦ rfl }
  let a : RingHom.ker q → R := fun s ↦ s
  have ha : RingHom.ker (algebraMap R S) = Ideal.span (Set.range a) := by
    change RingHom.ker q = Ideal.span (Set.range a)
    apply le_antisymm
    · intro x hx
      exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact s.property
  exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_of_isPerfectoidization_of_rootedGeneratingFamilyBaseChange
    hR hT hq hS hflat a ha ρ hρ0 hρ ff hf

end SerrePositivity.BhattScholze

end RootedFamilyPerfectoidSurjectivityDescent
