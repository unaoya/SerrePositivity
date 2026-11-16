module

public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaRing
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectDeltaResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilySource
public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.HomologicalAlgebra.TorDimensionShift
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorAnnihilator
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion

/-!
# 完全 prism 上の δ 代数の完全化（BS 著者版 Proposition 7.11(2) の「余極限へ移る」部分）

## 概要
δ 環射から Frobenius 環段とその係数加群、既存の δ 完全化への余錐、Frobenius 各段の prism 還元の次数消滅と忠実平坦性、完全化の剰余テンソルの平坦性・忠実性、逐次導来完備化と係数制限、PD 完備化 H⁰ への一意延長と比較、完全 prism 上での離散性、完全化後の PD 環の完全忠実平坦性。

## 方針
一般の δ 代数で述べるが、Frobenius 段の判定が `Envelope` の根添加源を経由するので Andre に置く（§3 の一般論として切り出すのは今後の候補）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicCandidate`、`Perfection/PerfectPrismMonic`、`PowerRootEnvelope/PerfectionFaithful`、`RootEnvelope/PerfectPrism`、`Variants/Auxiliary`、`Variants/RootedExtension`。
-/

universe u

/-! ## δ環射から実Frobenius環段の正確な係数加群へ -/

@[expose] public noncomputable section DeltaAlgebraFrobeniusStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B)

/-- 実Frobenius環段の係数射。基底作用を元のjと暗黙に同一視しない。 -/
def deltaAlgebraFrobeniusCoefficient (n : ℕ) : A →+* B := (E.frobeniusLift ^ n).comp j

/-- δ環射の自然性により、実段の係数作用は基底Frobeniusの制限作用と一致する。 -/
theorem deltaAlgebraFrobeniusCoefficient_apply (hj : D.IsDeltaHom E j) (n : ℕ) (a : A) :
    deltaAlgebraFrobeniusCoefficient E j n a = j ((D.frobeniusLift ^ n) a) := by
  change (E.frobeniusLift : B → B)^[n] (j a) = j ((D.frobeniusLift : A → A)^[n] a)
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hj.map_frobeniusLift]

/-- 正確なj_n作用を持つ実B段と、実基底Frobenius制限加群の恒等線形同型。 -/
def deltaAlgebraFrobeniusStageModuleIso (hj : D.IsDeltaHom E j) (n : ℕ) :
    (ModuleCat.restrictScalars (D.frobeniusLift ^ n)).obj (baseChangeScalarModule j) ≅
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) := by
  let e : (ModuleCat.restrictScalars (D.frobeniusLift ^ n)).obj (baseChangeScalarModule j) ≃ₗ[A]
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change j ((D.frobeniusLift ^ n) a) * x = deltaAlgebraFrobeniusCoefficient E j n a * x
        rw [deltaAlgebraFrobeniusCoefficient_apply D E j hj] }
  exact e.toModuleIso

/-- 同じ係数比較を、実導来制限と既存の実段single対象の比較へ持ち上げる。 -/
def deltaAlgebraFrobeniusStageSingleIso (hj : D.IsDeltaHom E j) (n : ℕ) :
    (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)).obj
      (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j)) ≅
        boundedAboveDerivedSingleFunctor.obj
          (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n)) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso (D.frobeniusLift ^ n) 0).app (baseChangeScalarModule j) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (deltaAlgebraFrobeniusStageModuleIso D E j hj n))

/-- 実φ_Bの隣接遷移は、各段の正確な係数作用についてA線形。 -/
def deltaAlgebraFrobeniusStageTransition (n : ℕ) :
    baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) ⟶
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) := by
  let f : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) →ₗ[A]
      baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) :=
    { toFun := fun x => E.frobeniusLift x
      map_add' := E.frobeniusLift.map_add
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change E.frobeniusLift (deltaAlgebraFrobeniusCoefficient E j n a * x) =
          deltaAlgebraFrobeniusCoefficient E j (n + 1) a * E.frobeniusLift x
        rw [map_mul]
        change E.frobeniusLift ((E.frobeniusLift : B → B)^[n] (j a)) * E.frobeniusLift x =
          (E.frobeniusLift : B → B)^[n + 1] (j a) * E.frobeniusLift x
        rw [Function.iterate_succ_apply'] }
  exact { hom' := f }

/-- 実Frobenius各環段の、正確な元A作用を持つ逐次加群図式。 -/
def deltaAlgebraFrobeniusStageModuleDiagram : ℕ ⥤ ModuleCat.{u} A :=
  Functor.ofSequence (fun n => deltaAlgebraFrobeniusStageTransition E j n)

/-- 図式の隣接射は、定義した実Frobenius遷移そのもの。 -/
theorem deltaAlgebraFrobeniusStageModuleDiagram_map_succ (n : ℕ) :
    (deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE (Nat.le_succ n)) =
      deltaAlgebraFrobeniusStageTransition E j n :=
  Functor.ofSequence_map_homOfLE_succ _ n

end SerrePositivity.BhattScholze

end DeltaAlgebraFrobeniusStages

/-! ## 実Frobenius環段から既存δ完全化への正確なA線形余錐 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionCocone

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B)

/-- 実δ完全化の元のA係数射は、既存の第0段標準射を通る。 -/
def deltaAlgebraPerfectionCoefficient : A →+* DeltaPerfection E :=
  (deltaPerfectionOf E 0).comp j

/-- 元の係数射がδ射なら、実δ完全化の同じ係数射もδ射。 -/
theorem deltaAlgebraPerfectionCoefficient_isDeltaHom (hj : D.IsDeltaHom E j) :
    D.IsDeltaHom (deltaPerfectionStructure E) (deltaAlgebraPerfectionCoefficient E j) :=
  (deltaPerfectionOf_isDeltaHom E 0).comp hj

/-- 全実段の係数像は、既存環余極限内で元のA係数像に一致する。 -/
theorem deltaAlgebraPerfectionOf_comp_coefficient (n : ℕ) :
    (deltaPerfectionOf E n).comp (deltaAlgebraFrobeniusCoefficient E j n) =
      deltaAlgebraPerfectionCoefficient E j := by
  apply RingHom.ext
  intro a
  change deltaPerfectionOf E n ((E.frobeniusLift : B → B)^[n] (j a)) =
    deltaPerfectionOf E 0 (j a)
  simpa only [Nat.sub_zero] using deltaPerfectionOf_iterate E (Nat.zero_le n) (j a)

/-- 既存環完全化への標準段射は、正確な元のA作用について線形。 -/
def deltaAlgebraPerfectionStageMap (n : ℕ) :
    baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) ⟶
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) := by
  let f : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) →ₗ[A]
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) :=
    { toFun := fun x => deltaPerfectionOf E n x
      map_add' := (deltaPerfectionOf E n).map_add
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change deltaPerfectionOf E n (deltaAlgebraFrobeniusCoefficient E j n a * x) =
          deltaAlgebraPerfectionCoefficient E j a * deltaPerfectionOf E n x
        rw [map_mul]
        exact congrArg (fun z => z * deltaPerfectionOf E n x)
          (RingHom.congr_fun (deltaAlgebraPerfectionOf_comp_coefficient E j n) a) }
  exact { hom' := f }

/-- A線形段射の値は、既存環余極限の元の標準射そのもの。 -/
theorem deltaAlgebraPerfectionStageMap_apply (n : ℕ)
    (x : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n)) :
    (deltaAlgebraPerfectionStageMap E j n).hom x = deltaPerfectionOf E n x := rfl

/-- 隣接する実Frobenius遷移は、環完全化への標準段射と可換。 -/
theorem deltaAlgebraPerfectionStageMap_transition (n : ℕ) :
    deltaAlgebraFrobeniusStageTransition E j n ≫ deltaAlgebraPerfectionStageMap E j (n + 1) =
      deltaAlgebraPerfectionStageMap E j n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B at x
  change deltaPerfectionOf E (n + 1) (E.frobeniusLift x) = deltaPerfectionOf E n x
  exact deltaPerfectionOf_succ_frobenius E n x

/-- 実環δ完全化の、元のA加群としての標準逐次余錐。 -/
def deltaAlgebraPerfectionModuleCocone :
    Cocone (deltaAlgebraFrobeniusStageModuleDiagram E j) where
  pt := baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
  ι := NatTrans.ofSequence (fun n => deltaAlgebraPerfectionStageMap E j n) (by
    intro n
    rw [deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
    exact deltaAlgebraPerfectionStageMap_transition E j n)

/-- 任意二段の実加群図式射は、元の実Frobenius反復を送る。 -/
theorem deltaAlgebraFrobeniusStageModuleDiagram_map_apply {i k : ℕ} (h : i ≤ k)
    (x : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j i)) :
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE h)).hom x =
      (E.frobeniusLift : B → B)^[k - i] x := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
      have he : homOfLE (Nat.le.step hik) =
          homOfLE hik ≫ homOfLE (Nat.le_succ k) := Subsingleton.elim _ _
      rw [he, Functor.map_comp, deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
      change E.frobeniusLift
        (((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom x) = _
      rw [ih]
      have hn : k + 1 - i = (k - i) + 1 := by omega
      rw [hn, Function.iterate_succ_apply']

/-- 標準A加群余錐は、既存実δ環完全化を頂点とする本当の逐次colimit。 -/
def deltaAlgebraPerfectionModuleCoconeIsColimit :
    IsColimit (deltaAlgebraPerfectionModuleCocone E j) := by
  let : DirectedSystem (fun _ : ℕ => B)
      (fun i k (_ : i ≤ k) => ((E.frobeniusLift ^ (k - i) : B →+* B) : B → B)) :=
    { map_self := by intro i x; simp
      map_map := by
        intro k l i hil hlk x
        change (E.frobeniusLift : B → B)^[k-l]
          ((E.frobeniusLift : B → B)^[l-i] x) = (E.frobeniusLift : B → B)^[k-i] x
        rw [← Function.iterate_add_apply]
        congr 1
        omega }
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : ReflectsColimit (deltaAlgebraFrobeniusStageModuleDiagram E j)
      (forget (ModuleCat.{u} A)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro y
    change DeltaPerfection E at y
    obtain ⟨n, x, rfl⟩ := Ring.DirectLimit.exists_of y
    exact ⟨n, x, rfl⟩
  · intro i x y hxy
    change B at x y
    change deltaPerfectionOf E i x = deltaPerfectionOf E i y at hxy
    have hz : deltaPerfectionOf E i (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨k, hik, hk⟩ := Ring.DirectLimit.of.zero_exact
      (G := fun _ : ℕ => B)
      (f' := fun (i k : ℕ) (_ : i ≤ k) => E.frobeniusLift ^ (k-i)) (i := i) (x := x-y) hz
    refine ⟨k, homOfLE hik, ?_⟩
    change ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom x =
      ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom y
    rw [deltaAlgebraFrobeniusStageModuleDiagram_map_apply,
      deltaAlgebraFrobeniusStageModuleDiagram_map_apply]
    change (E.frobeniusLift ^ (k-i)) x = (E.frobeniusLift ^ (k-i)) y
    exact sub_eq_zero.mp (by simpa only [map_sub] using hk)

/-- 実圏論的加群colimitは、元のA作用を持つ既存実δ完全化と同型。 -/
def deltaAlgebraPerfectionModuleColimitIso :
    colimit (deltaAlgebraFrobeniusStageModuleDiagram E j) ≅
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaAlgebraPerfectionModuleCoconeIsColimit E j)

/-- 標準colimit同型は、各実Frobenius段から既存環完全化への標準射を保つ。 -/
theorem deltaAlgebraPerfectionModuleColimitIso_ι (n : ℕ) :
    colimit.ι (deltaAlgebraFrobeniusStageModuleDiagram E j) n ≫
      (deltaAlgebraPerfectionModuleColimitIso E j).hom = deltaAlgebraPerfectionStageMap E j n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaAlgebraPerfectionModuleCoconeIsColimit E j) n

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionCocone

/-! ## 実Frobenius係数剰余へのprism冪剰余判定の接続 -/

@[expose] public noncomputable section PerfectDeltaPrismaticDerivedFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (n : ℕ)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "Jₙ" => Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "Qₙ" => A ⧸ Jₙ
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Jₙ)) X

/-- 元の実還元の次数零集中・忠実平坦性を、Frobeniusで動かした係数剰余へ渡す。 -/
theorem frobeniusPrismaticDerivedReduction_pure_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  let P (J : Ideal A) : Prop :=
    let Y := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X
    Y.obj.IsGE 0 ∧ Y.obj.IsLE 0 ∧ Module.FaithfullyFlat (A ⧸ J)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ J)) 0).obj Y.obj)
  have hpow : P (Ideal.span {(p : A), d ^ (p ^ n)}) :=
    prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d (p ^ n)
      (pow_pos (Fact.out : Nat.Prime p).pos n) X hzero hFF
  exact Eq.mp (congrArg P (frobeniusPrismaticResidueIdeal_eq D d n).symm) hpow

/-- 完全基底では、実φⁿの商係数作用で元のA/(p,d)へ制限したH0も忠実平坦。 -/
theorem perfectDeltaFrobeniusResidueH0_faithfullyFlat (hD : D.IsPerfect)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((ModuleCat.restrictScalars
        (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n).toRingHom).obj
          ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj)) := by
  let e := perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
  let M := (DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj
  let := e.toRingHom.toAlgebra
  let : Module Q₀ M := Module.compHom M e.toRingHom
  let : IsScalarTower Q₀ Qₙ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Q₀ ≃ₐ[Q₀] Qₙ := AlgEquiv.ofBijective (Algebra.ofId Q₀ Qₙ) e.bijective
  have : Module.FaithfullyFlat Q₀ Qₙ :=
    Module.FaithfullyFlat.of_linearEquiv Q₀ Q₀ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Qₙ M :=
    (frobeniusPrismaticDerivedReduction_pure_faithfullyFlat D d n X hzero hFF).2.2
  exact Module.FaithfullyFlat.trans Q₀ Qₙ M

/-- 完全prismの有限根族の実逐次源に対する、実Frobenius係数剰余の具体的入力。 -/
theorem perfectPrismRootFamilySource_frobenius_residue_inputs
    {σ : Type u} (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (b : σ → A) {m : ℕ} (s : Fin m ≃ σ) (k : ℕ) :
    let D₀ := P.deltaStructure
    let d₀ := P.generator
    let X₀ := _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D₀ d₀ b
    let Q := A ⧸ Ideal.span {(p : A), (D₀.frobeniusLift ^ k) d₀}
    let Y := (boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), (D₀.frobeniusLift ^ k) d₀}))).obj X₀
    (Y.obj.IsGE 0 ∧ Y.obj.IsLE 0 ∧ Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d₀})
        ((ModuleCat.restrictScalars
          (perfectDeltaFrobeniusPrismaticResidueEquiv D₀ hP d₀ k).toRingHom).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj)) := by
  let X₀ := _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
  have hz := _root_.SerrePositivity.BhattScholze.Andre.perfectPrismRootFamilySource_modPD_homology_isZero P hP b s
  have hf := _root_.SerrePositivity.BhattScholze.Andre.perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s
  exact ⟨frobeniusPrismaticDerivedReduction_pure_faithfullyFlat
      P.deltaStructure P.generator k X₀ hz hf,
    perfectDeltaFrobeniusResidueH0_faithfullyFlat P.deltaStructure P.generator k X₀ hP hz hf⟩

end SerrePositivity.BhattScholze

end PerfectDeltaPrismaticDerivedFlat

/-! ## 実Frobeniusねじれ段の標準prism還元の次数消滅と忠実平坦性 -/

@[expose] public noncomputable section PerfectDeltaFrobeniusStageFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section General
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (n : ℕ)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "κ" => RingEquiv.toRingHom
  (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n)
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {(p : A), (D.frobeniusLift ^ n) d}))) X
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) Zₙ
include hD

/-- 実ねじれ段の標準還元のホモロジーと、移動係数還元の正確な係数制限。 -/
def perfectDeltaFrobeniusTwistResidueHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Wₙ).obj ≅
      (ModuleCat.restrictScalars κ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Yₙ).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (perfectDeltaFrobeniusQuotientDerivedIso D hD d n X
          (boundedAboveDerivedChosenModel X))) ≪≫
    (derivedRestrictScalarsHomologyIso κ i).app (Yₙ).obj

/-- 元の実標準還元の性質から、ねじれ段の実標準還元の次数消滅を得る。 -/
theorem perfectDeltaFrobeniusTwistResidue_homology_isZero
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Wₙ).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    frobeniusPrismaticDerivedReduction_pure_faithfullyFlat D d n X hzero hFF
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Yₙ).obj) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
    · exact (DerivedCategory.isLE_iff _ _).mp hLE i h
  exact ((ModuleCat.restrictScalars κ).map_isZero hz).of_iso
    (perfectDeltaFrobeniusTwistResidueHomologyIso D hD d n X i)

/-- ねじれ段の実標準還元のH0は、同じ元のA/(p,d)上で忠実平坦。 -/
theorem perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Wₙ).obj) := by
  let M := (ModuleCat.restrictScalars κ).obj
    ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj)
  have : Module.FaithfullyFlat Q₀ M :=
    perfectDeltaFrobeniusResidueH0_faithfullyFlat D d n X hD hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M
    (perfectDeltaFrobeniusTwistResidueHomologyIso D hD d n X 0).toLinearEquiv
end General

/-- 完全prismの有限根族の実逐次源について、全実ねじれ段の標準還元入力。 -/
theorem perfectPrismRootFamilySource_frobenius_twist_inputs
    {σ : Type u} (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (b : σ → A) {m : ℕ} (s : Fin m ≃ σ) (k : ℕ) :
    let D := P.deltaStructure
    let d := P.generator
    let X := _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion D d b
    let Z := (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ k)).obj X
    let Q := A ⧸ Ideal.span {(p : A), d}
    let Y := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))).obj Z
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj Y.obj)) ∧
      Module.FaithfullyFlat Q
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj) := by
  let X := _root_.SerrePositivity.BhattScholze.Andre.DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
  have hz := _root_.SerrePositivity.BhattScholze.Andre.perfectPrismRootFamilySource_modPD_homology_isZero P hP b s
  have hf := _root_.SerrePositivity.BhattScholze.Andre.perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s
  exact ⟨perfectDeltaFrobeniusTwistResidue_homology_isZero
      P.deltaStructure hP P.generator k X hz hf,
    perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat P.deltaStructure hP P.generator k X hz hf⟩

end SerrePositivity.BhattScholze

end PerfectDeltaFrobeniusStageFlat

/-! ## 正確な係数作用を持つ実δ環段の標準還元判定 -/

@[expose] public noncomputable section DeltaAlgebraFrobeniusStageFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A) (n : ℕ)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Xₙ" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "Yₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) Xₙ
local notation "Wₙ" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀)
  (CategoryTheory.Functor.obj (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)) X₀)

/-- 元の実δ環の還元入力から、全実環段（j_n作用）の標準還元の次数消滅を得る。 -/
theorem deltaAlgebraFrobeniusStageResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Yₙ).obj) := by
  let e := (boundedAboveDerivedBaseChange q₀).mapIso
    (deltaAlgebraFrobeniusStageSingleIso D E j hj n).symm
  have hz := perfectDeltaFrobeniusTwistResidue_homology_isZero D hD d n X₀ hzero hFF i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso e))

/-- 正確なj_n係数作用を持つ全実環段の、標準還元H0忠実平坦性。 -/
theorem deltaAlgebraFrobeniusStageResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Yₙ).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Wₙ).obj
  let e := (boundedAboveDerivedBaseChange q₀).mapIso
    (deltaAlgebraFrobeniusStageSingleIso D E j hj n).symm
  let eH := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso e)
  have : Module.FaithfullyFlat Q₀ M :=
    perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat D hD d n X₀ hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M eH.toLinearEquiv

/-- 同じ実環段の通常の標準剰余テンソルも、元のA/(p,d)上で忠実平坦。 -/
theorem deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀ ((ModuleCat.extendScalars q₀).obj
      (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Yₙ).obj
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraFrobeniusStageResidueH0_faithfullyFlat D E j d n hD hj hzero hFF
  let e := (boundedAboveDerivedBaseChangeModuleH0Iso q₀).app
    (baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n))
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M e.toLinearEquiv.symm

end SerrePositivity.BhattScholze

end DeltaAlgebraFrobeniusStageFlat

/-! ## 実δ完全化への余極限との比較の適用 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionTor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M∞
local notation "Y∞" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X∞

/-- 各実δ環段の標準還元入力を、余極限との比較により実δ完全化の正のTorへ渡す。 -/
theorem deltaAlgebraPerfectionResidueTor_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (hn : 0 < n) :
    IsZero (((ModuleCat.extendScalars q₀).leftDerived n).obj M∞) := by
  let H := (ModuleCat.extendScalars q₀).leftDerived n
  have hz : IsZero (H.obj (colimit (deltaAlgebraFrobeniusStageModuleDiagram E j))) := by
    apply torAlg_colimit_isZero_of_stages
    intro k
    let M := baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j k)
    let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
        (boundedAboveDerivedBaseChangeModuleIso q₀ M) ≪≫
      (derivedModuleBaseChangeHomologyIso q₀ n).app M
    have h := deltaAlgebraFrobeniusStageResidue_homology_isZero
      D E j d k hD hj hzero hFF (-(n : ℤ)) (by omega)
    exact h.of_iso e.symm
  exact hz.of_iso (H.mapIso (deltaAlgebraPerfectionModuleColimitIso E j)).symm

/-- 実δ完全化の同じ標準導来還元は、全負次数でホモロジーが消える。 -/
theorem deltaAlgebraPerfectionResidue_negativeHomology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (hn : 0 < n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).obj (Y∞).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso q₀ M∞) ≪≫
    (derivedModuleBaseChangeHomologyIso q₀ n).app M∞
  exact (deltaAlgebraPerfectionResidueTor_isZero D E j d hD hj hzero hFF n hn).of_iso e

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionTor

/-! ## 実δ完全化の標準剰余テンソルの平坦性 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionResidueFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)

/-- 既存実δ完全化の標準剰余テンソルと、実各段の剰余テンソルのcolimitの同型。 -/
def deltaAlgebraPerfectionResidueColimitIso :
    colimit (deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀) ≅
      (ModuleCat.extendScalars q₀).obj M∞ :=
  (preservesColimitIso (ModuleCat.extendScalars q₀)
      (deltaAlgebraFrobeniusStageModuleDiagram E j)).symm ≪≫
    (ModuleCat.extendScalars q₀).mapIso (deltaAlgebraPerfectionModuleColimitIso E j)

/-- 元の実還元入力から、実δ完全化の同じ標準剰余テンソルの通常平坦性を得る。 -/
theorem deltaAlgebraPerfectionResidueTensor_flat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.Flat Q₀ ((ModuleCat.extendScalars q₀).obj M∞) := by
  let F := deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀
  let M := (ModuleCat.extendScalars q₀).obj M∞
  have ht (N : Type u) [AddCommGroup N] [Module Q₀ N] :
      Subsingleton (TorModule Q₀ 1 M N) := by
    let H := (Tor (ModuleCat Q₀) 1).obj (ModuleCat.of Q₀ N)
    let : PreservesColimitsOfShape ℕ H := tor_preservesSequentialColimits _ 1
    have hz : IsZero (colimit (F ⋙ H)) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply colimit.hom_ext
      intro k
      have hF := deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
        D E j d k hD hj hzero hFF
      let : Module.Flat Q₀ (F.obj k) := hF.1
      have : Subsingleton (TorModule Q₀ 1 (F.obj k) N) :=
        torModule_subsingleton_of_flat (F.obj k) N 0
      have : Subsingleton (TorModule Q₀ 1 N (F.obj k)) :=
        (torModuleComm (R := Q₀) 1 N (F.obj k)).injective.subsingleton
      have hzK : IsZero (H.obj (ModuleCat.of Q₀ (F.obj k))) :=
        ModuleCat.isZero_of_subsingleton _
      exact hzK.eq_of_src _ _
    have hlim : IsZero (H.obj (colimit F)) := hz.of_iso (preservesColimitIso H F)
    have hM : IsZero (H.obj M) :=
      hlim.of_iso (H.mapIso (deltaAlgebraPerfectionResidueColimitIso E j d)).symm
    have : Subsingleton (TorModule Q₀ 1 N M) := ModuleCat.subsingleton_of_isZero hM
    exact (torModuleComm (R := Q₀) 1 M N).injective.subsingleton
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  exact lTensor_injective_of_torModule_one M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range (ht (N' ⧸ f.range))

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionResidueFlat

/-! ## 実Frobenius各段の標準剰余の単位と忠実性 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionResidueFaithful

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "F₀" => deltaAlgebraFrobeniusStageModuleDiagram E j ⋙ ModuleCat.extendScalars q₀

/-- 各実段の標準剰余内の、元の環単位から来る元。 -/
def deltaAlgebraFrobeniusStageResidueUnit (n : ℕ) : (F₀).obj n :=
  (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
    (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) from (1 : B))

/-- 標準剰余の各隣接射は元の環単位を保つ。 -/
theorem deltaAlgebraFrobeniusStageResidueUnit_succ (n : ℕ) :
    (F₀).map (homOfLE (Nat.le_succ n)) (deltaAlgebraFrobeniusStageResidueUnit E j d n) =
      deltaAlgebraFrobeniusStageResidueUnit E j d (n + 1) := by
  change (ModuleCat.extendScalars q₀).map
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE (Nat.le_succ n))) _ = _
  rw [deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
  simp only [deltaAlgebraFrobeniusStageResidueUnit, ModuleCat.ExtendScalars.map_tmul]
  apply congrArg (fun b : B =>
    (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
      (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j (n + 1)) from b))
  exact E.frobeniusLift.map_one

/-- 正確な標準剰余の単位によるテンソル写像は、各実環段で単射。 -/
theorem deltaAlgebraFrobeniusStageResidue_unitTensor_injective
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (n : ℕ) (N : Type u) [AddCommGroup N] [Module Q₀ N] :
    Function.Injective (TensorProduct.mk Q₀ ((F₀).obj n) N
      (deltaAlgebraFrobeniusStageResidueUnit E j d n)) := by
  let : Algebra A B := (deltaAlgebraFrobeniusCoefficient E j n).toAlgebra
  let : Algebra A Q₀ := (q₀).toAlgebra
  have h := deltaAlgebraFrobeniusStageResidueTensor_faithfullyFlat
    D E j d n hD hj hzero hFF
  let : Module.FaithfullyFlat Q₀ (Q₀ ⊗[A] B) := h
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := Q₀) (B := Q₀ ⊗[A] B) N

/-- 任意二段の標準剰余射も、元の環単位を保つ。 -/
theorem deltaAlgebraFrobeniusStageResidueUnit_map {i k : ℕ} (h : i ≤ k) :
    (F₀).map (homOfLE h) (deltaAlgebraFrobeniusStageResidueUnit E j d i) =
      deltaAlgebraFrobeniusStageResidueUnit E j d k := by
  change (ModuleCat.extendScalars q₀).map
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE h)) _ = _
  simp only [deltaAlgebraFrobeniusStageResidueUnit, ModuleCat.ExtendScalars.map_tmul]
  rw [deltaAlgebraFrobeniusStageModuleDiagram_map_apply]
  apply congrArg (fun b : B =>
    (show baseChangeScalarModule q₀ from (1 : Q₀)) ⊗ₜ[A]
      (show baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j k) from b))
  exact (E.frobeniusLift ^ (k - i)).map_one

/-- 単位を保つ実図式の有限段検出により、実δ完全化の標準剰余は忠実平坦。 -/
theorem deltaAlgebraPerfectionResidueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀ ((ModuleCat.extendScalars q₀).obj
      (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))) := by
  let M := (ModuleCat.extendScalars q₀).obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Q₀ M).mpr
  refine ⟨deltaAlgebraPerfectionResidueTensor_flat D E j d hD hj hzero hFF, ?_⟩
  intro N _ _ hN
  let F := F₀
  let H := tensorRight (ModuleCat.of Q₀ N)
  let K := F ⋙ H
  let e : colimit K ≅ H.obj M :=
    (preservesColimitIso H F).symm ≪≫
      H.mapIso (deltaAlgebraPerfectionResidueColimitIso E j d)
  have : Subsingleton (N ⊗[Q₀] M) := hN
  have : Subsingleton (M ⊗[Q₀] N) := (TensorProduct.comm Q₀ M N).injective.subsingleton
  have : Subsingleton (H.obj M) := by
    change Subsingleton (M ⊗[Q₀] N)
    infer_instance
  have : Subsingleton (colimit K : ModuleCat Q₀) := e.toLinearEquiv.injective.subsingleton
  let U := forget (ModuleCat.{u} Q₀)
  let : PreservesFilteredColimitsOfSize.{0, 0} U :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ht := isColimitOfPreserves U (colimit.isColimit K)
  refine ⟨fun x y => ?_⟩
  let z := deltaAlgebraFrobeniusStageResidueUnit E j d 0
  have heq : (U.mapCocone (colimit.cocone K)).ι.app 0 (z ⊗ₜ[Q₀] x) =
      (U.mapCocone (colimit.cocone K)).ι.app 0 (z ⊗ₜ[Q₀] y) := by
    change (colimit.ι K 0).hom (z ⊗ₜ[Q₀] x) = (colimit.ι K 0).hom (z ⊗ₜ[Q₀] y)
    exact Subsingleton.elim _ _
  obtain ⟨k, f, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' ht
    (z ⊗ₜ[Q₀] x) (z ⊗ₜ[Q₀] y)).mp heq
  have hf : f = homOfLE (Nat.zero_le k) := Subsingleton.elim _ _
  subst f
  change (F.map (homOfLE (Nat.zero_le k))).hom.rTensor N (z ⊗ₜ[Q₀] x) =
    (F.map (homOfLE (Nat.zero_le k))).hom.rTensor N (z ⊗ₜ[Q₀] y) at hk
  rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul] at hk
  dsimp only [z] at hk
  rw [deltaAlgebraFrobeniusStageResidueUnit_map] at hk
  exact deltaAlgebraFrobeniusStageResidue_unitTensor_injective
    D E j d hD hj hzero hFF k N hk

/-- 忠実平坦な通常標準剰余を、同じ実導来還元のH0へ戻す。 -/
theorem deltaAlgebraPerfectionResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj
          (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)))).obj) := by
  let M := (ModuleCat.extendScalars q₀).obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraPerfectionResidueTensor_faithfullyFlat D E j d hD hj hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M
    ((boundedAboveDerivedBaseChangeModuleH0Iso q₀).app
      (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))).toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionResidueFaithful

/-! ## 実δ完全化の標準還元の次数零比較 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M∞
local notation "Y∞" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X∞
/-- 同じ実標準係数射について、既存augmentation判定へのTor入力を供給する。 -/
theorem deltaAlgebraPerfectionResidue_scalarExtensionTorVanishing
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    scalarExtensionTorVanishing q₀ M∞ := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q₀ M∞).mp
  intro n hn
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) (-(n : ℤ))).mapIso
    (boundedAboveDerivedBaseChangeModuleIso q₀ M∞)
  exact (deltaAlgebraPerfectionResidue_negativeHomology_isZero
    D E j d hD hj hzero hFF n hn).of_iso e.symm

/-- 実δ完全化の標準還元は、既存標準augmentationにより実剰余テンソルのsingleと同型。 -/
def deltaAlgebraPerfectionResidueAugmentationIso
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Y∞ ≅ boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q₀).obj M∞) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso q₀ M∞
    (deltaAlgebraPerfectionResidue_scalarExtensionTorVanishing D E j d hD hj hzero hFF)

/-- 実δ完全化の同じ標準導来還元の、全非零次数ホモロジー消滅。 -/
theorem deltaAlgebraPerfectionResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y∞).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaAlgebraPerfectionResidueAugmentationIso D E j d hD hj hzero hFF))
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q₀).obj M∞) i hi).of_iso e

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionResidue

/-! ## 実δ完全化の逐次導来完備化の標準還元 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionCompletionResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
local notation "M∞" => baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M∞
local notation "Y∞" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X∞
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 同じ実δ完全化の正確なA加群を、既存の実p,d関手で逐次完備化した対象。 -/
abbrev DeltaAlgebraPerfectionIteratedPDCompletion := (Cd).obj ((Cp).obj X∞)

/-- 個別に正則なp,dについて、逐次完備化後の実還元は未完備還元と比較できる。 -/
def deltaAlgebraPerfectionCompletionReductionIso
    (hp : IsSMulRegular A (p : A)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).obj (DeltaAlgebraPerfectionIteratedPDCompletion E j d) ≅
      Y∞ :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hp hd X∞

/-- 還元比較は、二つの元の標準完備化単位の合成を保つ。 -/
theorem deltaAlgebraPerfectionCompletionReductionIso_unit
    (hp : IsSMulRegular A (p : A)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞)) ≫
      (deltaAlgebraPerfectionCompletionReductionIso E j d hp hd).hom = 𝟙 _ :=
  prismaticCoefficientIteratedCompletionPairIso_unit (p : A) d hp hd X∞

/-- 実δ完全化の逐次導来完備化後の標準還元の全非零次数は零。 -/
theorem deltaAlgebraPerfectionCompletionResidue_homology_isZero
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j) (hd : IsSMulRegular A d)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (DeltaAlgebraPerfectionIteratedPDCompletion E j d)).obj) :=
  (deltaAlgebraPerfectionResidue_homology_isZero D E j d hD hj hzero hFF i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaAlgebraPerfectionCompletionReductionIso E j d hD.p_mul_injective hd)))

/-- 同じ逐次完備化後の実標準還元H0は、正確なA/(p,d)上で忠実平坦。 -/
theorem deltaAlgebraPerfectionCompletionResidueH0_faithfullyFlat
    (hD : D.IsPerfect) (hj : D.IsDeltaHom E j) (hd : IsSMulRegular A d)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj
          (DeltaAlgebraPerfectionIteratedPDCompletion E j d)).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y∞).obj
  have : Module.FaithfullyFlat Q₀ M :=
    deltaAlgebraPerfectionResidueH0_faithfullyFlat D E j d hD hj hzero hFF
  let e := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaAlgebraPerfectionCompletionReductionIso E j d hD.p_mul_injective hd))
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M e.toLinearEquiv

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionCompletionResidue

/-! ## 完全prism上の実δ完全化逐次対象の完備性と還元入力 -/

@[expose] public noncomputable section PerfectPrismDeltaAlgebraCompletionInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)

/-- 同じ実δ完全化の逐次対象は、d完備化後もp導来完備。 -/
theorem deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p :
    IsComplete A (p : A) (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj := by
  let X := boundedAboveDerivedSingleFunctor.obj
    (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j))
  let Y := (boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : IsComplete A (p : A) Y.obj :=
    derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : IsComplete A (p : A)
      (DerivedCategory.Q.obj (complexPowerKoszulStage A d K n)) :=
    isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  have hC : IsComplete A (p : A) (complexCompletionObject A d K) :=
    isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (complexPowerKoszulStage A d K) (complexPowerKoszulTransition A d K) hstage
  let e : complexCompletionObject A d K ≅
      (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj :=
    (derivedComplexCompletionComparison A d).symm.app K ≪≫
      (derivedComplexCompletionFunctor A d).mapIso eK
  exact isComplete_of_iso A (p : A) e hC

/-- 同じ具体的逐次対象は、最後の主元完備化によりd導来完備。 -/
theorem deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d :
    IsComplete A d (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj :=
  derivedComplexCompletionFunctor_isComplete A d
    ((boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (boundedAboveDerivedSingleFunctor.obj
        (baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)))).obj

/-- 完全prism上の実逐次対象の完備性と還元入力。元Bの還元条件は明示する。 -/
theorem perfectPrismDeltaAlgebraCompletion_residue_inputs
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj)) :
    let X := DeltaAlgebraPerfectionIteratedPDCompletion E j P.generator
    let Y := (boundedAboveDerivedBaseChange
      (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj X
    IsComplete A (p : A) X.obj ∧ IsComplete A P.generator X.obj ∧
      (∀ i : ℤ, i ≠ 0 → IsZero
        ((DerivedCategory.homologyFunctor
          (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj Y.obj)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
        ((DerivedCategory.homologyFunctor
          (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj Y.obj) := by
  refine ⟨deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p E j P.generator,
    deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d E j P.generator, ?_, ?_⟩
  · exact deltaAlgebraPerfectionCompletionResidue_homology_isZero
      P.deltaStructure E j P.generator hP hj P.generator_regular hzero hFF
  · exact deltaAlgebraPerfectionCompletionResidueH0_faithfullyFlat
      P.deltaStructure E j P.generator hP hj P.generator_regular hzero hFF

end SerrePositivity.BhattScholze

end PerfectPrismDeltaAlgebraCompletionInputs

/-! ## 実δ完全化逐次対象の生成元冪商のp導来完備性 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionPowerComplete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d

/-- 同じ実δ完全化逐次対象の生成元冪商を、元の係数上の実Koszul錐へ比較する。 -/
def deltaAlgebraPerfectionGeneratorPowerReductionKoszulIso
    (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X)).obj ≅
        (derivedScalarConeFunctor A (d ^ n)).obj (X).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X

/-- 正則生成元の任意冪商への同じ実還元は、その商環上でp導来完備。 -/
theorem deltaAlgebraPerfectionGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj X).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) := by
    let K := DerivedCategory.Q.objPreimage (X).obj
    let eK : DerivedCategory.Q.obj K ≅ (X).obj := DerivedCategory.Q.objObjPreimageIso (X).obj
    have hK : IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
      isComplete_of_iso A (p : A) eK.symm
        (deltaAlgebraPerfectionIteratedPDCompletion_isComplete_p E j d)
    have hC := isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
    let e := deltaAlgebraPerfectionGeneratorPowerReductionKoszulIso E j d hd n ≪≫
      (derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
        (derivedScalarConeComparison A (d ^ n)).app K
    exact isComplete_of_iso A (p : A) e.symm hC
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

end DeltaAlgebraPerfectionPowerComplete

/-! ## 実δ完全化逐次対象の生成元冪商上の離散性の判定入力 -/

@[expose] public noncomputable section PerfectPrismDeltaAlgebraPowerInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B) (n : ℕ)
local notation "d" => OrientedPrism.generator P
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X₀
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ

/-- 冪零還元からの純性・平坦性の判定と標準商比較により、同じ生成元冪商上のmod p還元は次数零・H0平坦。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_modP_inputs
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n) :
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨_, _, hz, hff⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  obtain ⟨hGE, hLE, hFlat⟩ :=
    prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d n hn X hz hff
  refine ⟨?_, prismaticGeneratorPowerModPH0_flat p d n X hFlat.1⟩
  intro i hi
  apply prismaticGeneratorPowerModP_homology_isZero p d n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 同じ実冪商対象について、完備性・係数ねじれ上界・標準mod p入力を供給する。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_G9_inputs
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n) :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ k : ℕ, ∀ x : Tₙ, (p : Tₙ) ^ k * x = 0 → (p : Tₙ) ^ n * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hz, hflat⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_modP_inputs P E j n hP hj hzero hFF hn
  refine ⟨deltaAlgebraPerfectionGeneratorPowerReduction_isComplete_over_quotient
    E j d P.generator_regular n, ?_, hz, hflat⟩
  let := P.isAdicComplete_p_of_perfect hP
  intro k x hx
  exact hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (P.isDistinguished_generator) n k x hx

/-- 還元と余核の比較の元の選択モデルのp余核複体へ、同じ実標準還元の消滅を渡す。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_modP_cokernel_homology_isZero
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCompletion.powerCokernelComplex (p : Tₙ)
      (boundedAboveDerivedChosenModel Zₙ).complex 1).homology i) := by
  apply DerivedCompletion.powerCokernel_homology_isZero_of_reduction (p : Tₙ) 1 Zₙ i
  let H (a : Tₙ) := IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (Tₙ ⧸ Ideal.span {a})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj Zₙ).obj)
  have hz : H (p : Tₙ) :=
    (perfectPrismDeltaAlgebraCompletionPower_modP_inputs P E j n hP hj hzero hFF hn).1 i hi
  exact Eq.mp (congrArg H (_root_.pow_one (p : Tₙ)).symm) hz

end SerrePositivity.BhattScholze

end PerfectPrismDeltaAlgebraPowerInputs

/-! ## 完全prism上の実δ完全化逐次対象の離散性 -/

@[expose] public noncomputable section PerfectPrismDeltaAlgebraDiscrete

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "d" => OrientedPrism.generator P
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
include hP hj hzero hFF

/-- 同じ実δ完全化逐次対象の生成元冪商は離散でH0は有界p冪ねじれを持つ。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion (n : ℕ) (hn : 0 < n) :
    let T := A ⧸ Ideal.span {d ^ n}
    let Z := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X
    Z.obj.IsGE 0 ∧ Z.obj.IsLE 0 ∧
      ∃ N : ℕ, ∀ k : ℕ,
        ∀ z : (DerivedCategory.homologyFunctor (ModuleCat.{u} T) 0).obj Z.obj,
          (p : T) ^ k • z = 0 → (p : T) ^ N • z = 0 := by
  obtain ⟨hc, ht, hz, hf⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_G9_inputs P E j n hP hj hzero hFF hn
  exact derived_pure_bounded_torsion_of_complete_flat_reduction _ _ hz hf ⟨n, ht⟩ hc

/-- 同じ生成元冪商の非零次数ホモロジーは零。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_homology_isZero
    (n : ℕ) (hn : 0 < n) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d ^ n})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_pure_bounded_torsion P E j hP hj hzero hFF n hn
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 実δ完全化の生成元冪余核は、零冪を含め全負次数で消える。 -/
theorem perfectPrismDeltaAlgebraCompletion_powerCokernel_homology_isZero
    (n : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((powerCokernelComplex d (boundedAboveDerivedChosenModel X).complex n).homology i) := by
  apply powerCokernel_homology_isZero_of_reduction d n X i
  by_cases hn : 0 < n
  · exact perfectPrismDeltaAlgebraCompletionPower_homology_isZero
      P E j hP hj hzero hFF n hn i (by omega)
  · have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton (A ⧸ Ideal.span {d ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact Module.subsingleton (A ⧸ Ideal.span {d ^ 0}) _

/-- 完全prism上の実δ完全化逐次対象は離散。 -/
theorem perfectPrismDeltaAlgebraCompletion_pure :
    (X).obj.IsGE 0 ∧ (X).obj.IsLE 0 := by
  have hmod (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {d})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d}))).obj X).obj) := by
    let F (t : A) := IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {t})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {t}))).obj X).obj)
    exact Eq.mp (congrArg F (pow_one d))
      (perfectPrismDeltaAlgebraCompletionPower_homology_isZero
          P E j hP hj hzero hFF 1 (by omega) i hi)
  obtain ⟨hGE, hLE, _⟩ := derived_pure_of_complete_regular_quotient_pure d
    P.generator_regular X (deltaAlgebraPerfectionIteratedPDCompletion_isComplete_d E j d) hmod
  exact ⟨hGE, hLE⟩

/-- 同じ実δ完全化逐次対象をその実H0のsingleに正規化して同定する。 -/
def perfectPrismDeltaAlgebraCompletionSingleIso :
    (X).obj ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj (X).obj) := by
  obtain ⟨hGE, hLE⟩ := perfectPrismDeltaAlgebraCompletion_pure P E j hP hj hzero hFF
  let := hGE
  let := hLE
  exact normalizedPureHomologyIso (X).obj 0

end SerrePositivity.BhattScholze

end PerfectPrismDeltaAlgebraDiscrete

/-! ## 実δ完全化の逐次完備化と正確な係数制限の比較 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionCompletionRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "C∞" => DeltaPerfection E
local notation "κ∞" => deltaAlgebraPerfectionCoefficient E j
local notation "R∞" => boundedAboveDerivedRestrictScalars κ∞
local notation "S∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (ModuleCat.of C∞ C∞)
local notation "X∞" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ∞)
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d
local notation "Cp∞" => boundedAboveDerivedCompletionFunctor C∞ (κ∞ (p : A))
local notation "Cd∞" => boundedAboveDerivedCompletionFunctor C∞ (κ∞ d)
local notation "Up∞" => boundedAboveDerivedCompletionUnit C∞ (κ∞ (p : A))
local notation "Ud∞" => boundedAboveDerivedCompletionUnit C∞ (κ∞ d)

/-- 元のC上のsingleの係数制限は、正確なA作用を持つ既存のsingleと同型。 -/
def deltaAlgebraPerfectionSingleRestrictionIso : (R∞).obj S∞ ≅ X∞ :=
  ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ∞ 0).app (ModuleCat.of C∞ C∞))

/-- 共通係数制限と完備化の比較を両方向へ適用した、同じ実逐次完備化対象の比較。 -/
def deltaAlgebraPerfectionCompletionRestrictionIso :
    DeltaAlgebraPerfectionIteratedPDCompletion E j d ≅
      (R∞).obj ((Cd∞).obj ((Cp∞).obj S∞)) :=
  (Cd).mapIso ((Cp).mapIso (deltaAlgebraPerfectionSingleRestrictionIso E j).symm ≪≫
      (boundedAboveCompletionRestrictionIso κ∞ (p : A)).app S∞) ≪≫
    (boundedAboveCompletionRestrictionIso κ∞ d).app ((Cp∞).obj S∞)

/-- 逐次係数制限と完備化の比較比較は、元の両完備化単位の合成を保つ。 -/
theorem deltaAlgebraPerfectionCompletionRestrictionIso_unit :
    (((Up).app X∞) ≫ (Ud).app ((Cp).obj X∞)) ≫
        (deltaAlgebraPerfectionCompletionRestrictionIso E j d).hom =
      (deltaAlgebraPerfectionSingleRestrictionIso E j).inv ≫
        (R∞).map (((Up∞).app S∞) ≫ (Ud∞).app ((Cp∞).obj S∞)) := by
  let e := (Cp).mapIso (deltaAlgebraPerfectionSingleRestrictionIso E j).symm ≪≫
    (boundedAboveCompletionRestrictionIso κ∞ (p : A)).app S∞
  have hp : (Up).app X∞ ≫ e.hom =
      (deltaAlgebraPerfectionSingleRestrictionIso E j).inv ≫
        (R∞).map ((Up∞).app S∞) := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
    rw [← Category.assoc, ← (Up).naturality]
    simp only [Functor.id_map, Category.assoc]
    rw [boundedAboveCompletionRestrictionIso_unit]
  have hn := (Ud).naturality e.hom
  simp only [Functor.id_map] at hn
  change ((Up).app X∞ ≫ (Ud).app ((Cp).obj X∞)) ≫
    ((Cd).map e.hom ≫ (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) = _
  calc
    _ = (Up).app X∞ ≫
        (((Ud).app ((Cp).obj X∞) ≫ (Cd).map e.hom) ≫
          (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) := by
      simp only [Category.assoc]
    _ = ((Up).app X∞ ≫ e.hom) ≫
        ((Ud).app ((R∞).obj ((Cp∞).obj S∞)) ≫
          (boundedAboveCompletionRestrictionIso κ∞ d).hom.app _) := by
      rw [← hn]
      simp only [Category.assoc, Functor.comp_obj]
    _ = _ := by
      rw [hp, boundedAboveCompletionRestrictionIso_unit, Functor.map_comp]
      simp only [Category.assoc]

/-- 同じ実逐次対象のH0も、元のκ作用を保ったC上のH0の制限と同型。 -/
def deltaAlgebraPerfectionCompletionRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaAlgebraPerfectionIteratedPDCompletion E j d).obj ≅
      (ModuleCat.restrictScalars κ∞).obj
        ((DerivedCategory.homologyFunctor (ModuleCat C∞) 0).obj
          ((Cd∞).obj ((Cp∞).obj S∞)).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaAlgebraPerfectionCompletionRestrictionIso E j d)) ≪≫
    (derivedRestrictScalarsHomologyIso κ∞ 0).app (((Cd∞).obj ((Cp∞).obj S∞)).obj)

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionCompletionRestriction

/-! ## 実δ完全化逐次対象から直接PD完備化H0への標準一意延長 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionPDCompletionMap

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule κ)
local notation "Y" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule t)
local notation "Cp" => boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => boundedAboveDerivedCompletionFunctor A d
local notation "Up" => boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => boundedAboveDerivedCompletionUnit A d

/-- 直接PD完備化の元の標準環射は、元Aの正確な作用について線形。 -/
def deltaAlgebraPerfectionPDCompletionLinearMap :
    letI := pdCompletionCommRing C p (κ d)
    baseChangeScalarModule κ ⟶ baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  let f : baseChangeScalarModule κ →ₗ[A] baseChangeScalarModule t :=
    { toFun := fun c => s c
      map_add' := (s).map_add
      map_smul' := by
        intro a c
        change C at c
        rw [RingHom.id_apply]
        change s (κ a * c) = s (κ a) * s c
        exact (s).map_mul _ _ }
  exact { hom' := f }

/-- 同じ標準環射を元A上の実single射へ移す。 -/
def deltaAlgebraPerfectionPDCompletionSingleMap :
    letI := pdCompletionCommRing C p (κ d)
    X ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact boundedAboveDerivedSingleFunctor.map (deltaAlgebraPerfectionPDCompletionLinearMap E j d)

/-- 直接PD完備化H0の同じA作用付きsingleはp導来完備。 -/
theorem deltaAlgebraPerfectionPDCompletionSingle_isComplete_p :
    letI := pdCompletionCommRing C p (κ d)
    IsComplete A (p : A) (Y).obj := by
  let := pdCompletionCommRing C p (κ d)
  change IsModuleComplete A (p : A) (baseChangeScalarModule t)
  have h := pdCompletionH0_self_complete_p C p (κ d)
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  change Function.Bijective (fun z : ℕ → H => fun n => z n - t (p : A) * z (n + 1))
  change Function.Bijective (fun z : ℕ → H => fun n => z n - (p : H) * z (n + 1)) at h
  simpa only [map_natCast] using h

/-- 同じA作用付きsingleは元Aのdについても導来完備。 -/
theorem deltaAlgebraPerfectionPDCompletionSingle_isComplete_d :
    letI := pdCompletionCommRing C p (κ d)
    IsComplete A d (Y).obj := by
  let := pdCompletionCommRing C p (κ d)
  change IsModuleComplete A d (baseChangeScalarModule t)
  have h := pdCompletionH0_self_complete_d C p (κ d)
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  exact h

/-- 同じ標準single射を、実p完備化後から一意延長する。 -/
def deltaAlgebraPerfectionPDCompletionPMap :
    letI := pdCompletionCommRing C p (κ d)
    (Cp).obj X ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)).symm
        (deltaAlgebraPerfectionPDCompletionSingleMap E j d).hom)

/-- p方向の一意延長は、元の実標準単位を保つ。 -/
theorem deltaAlgebraPerfectionPDCompletionPMap_unit :
    letI := pdCompletionCommRing C p (κ d)
    (Up).app X ≫ deltaAlgebraPerfectionPDCompletionPMap E j d =
      deltaAlgebraPerfectionPDCompletionSingleMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  apply InducedCategory.hom_ext
  exact (derivedComplexCompletionHomEquiv A (p : A) (X).obj (Y).obj
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)).apply_symm_apply
      (deltaAlgebraPerfectionPDCompletionSingleMap E j d).hom

/-- 実δ完全化の同じ実逐次対象から、直接PD完備化H0のsingleへの標準射。 -/
def deltaAlgebraPerfectionPDCompletionIteratedMap :
    letI := pdCompletionCommRing C p (κ d)
    DeltaAlgebraPerfectionIteratedPDCompletion E j d ⟶ Y := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.homMk
    ((derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)).symm
        (deltaAlgebraPerfectionPDCompletionPMap E j d).hom)

/-- 両実標準単位の合成は、元の標準環射からのsingle射を保つ。 -/
theorem deltaAlgebraPerfectionPDCompletionIteratedMap_unit :
    letI := pdCompletionCommRing C p (κ d)
    ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫
        deltaAlgebraPerfectionPDCompletionIteratedMap E j d =
      deltaAlgebraPerfectionPDCompletionSingleMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  have h : (Ud).app ((Cp).obj X) ≫ deltaAlgebraPerfectionPDCompletionIteratedMap E j d =
      deltaAlgebraPerfectionPDCompletionPMap E j d := by
    apply InducedCategory.hom_ext
    exact (derivedComplexCompletionHomEquiv A d ((Cp).obj X).obj (Y).obj
      (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)).apply_symm_apply
        (deltaAlgebraPerfectionPDCompletionPMap E j d).hom
  rw [Category.assoc, h, deltaAlgebraPerfectionPDCompletionPMap_unit]

/-- 同じ両単位上で元の標準射に一致する延長は、この具体的標準延長だけである。 -/
theorem deltaAlgebraPerfectionPDCompletionIteratedMap_unique :
    letI := pdCompletionCommRing C p (κ d)
    ∀ g : DeltaAlgebraPerfectionIteratedPDCompletion E j d ⟶ Y,
      ((Up).app X ≫ (Ud).app ((Cp).obj X)) ≫ g =
        deltaAlgebraPerfectionPDCompletionSingleMap E j d →
      g = deltaAlgebraPerfectionPDCompletionIteratedMap E j d := by
  let := pdCompletionCommRing C p (κ d)
  intro g hg
  have he : (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫ g) =
      (Up).app X ≫ ((Ud).app ((Cp).obj X) ≫
        deltaAlgebraPerfectionPDCompletionIteratedMap E j d) := by
    simpa only [Category.assoc] using
      hg.trans (deltaAlgebraPerfectionPDCompletionIteratedMap_unit E j d).symm
  apply InducedCategory.hom_ext
  apply derivedComplexCompletionHom_ext A d
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_d E j d)
  apply derivedComplexCompletionHom_ext A (p : A)
    (deltaAlgebraPerfectionPDCompletionSingle_isComplete_p E j d)
  exact congrArg (fun f => f.hom) he

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionPDCompletionMap

/-! ## 実δ完全化逐次H0から正確なPD係数加群への比較 -/

@[expose] public noncomputable section DeltaAlgebraPerfectionPDH0Comparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (E : DeltaStructure p B) (j : A →+* B) (d : A)
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ) (ModuleCat.of C H)
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d

/-- 実PD H0の制限加群は、元の標準合成係数射に沿う加群と同型。 -/
def deltaAlgebraPerfectionPDNativeModuleIso :
    letI := pdCompletionCommRing C p (κ d)
    M ≅ baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  let := pdCompletionAlgebra C p (κ d)
  let Mc : ModuleCat.{u} A := M
  let Nc : ModuleCat.{u} A := baseChangeScalarModule t
  let f : Mc →ₗ[A] Nc :=
    { toFun := (id : H → H)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change H at x
        change (κ a) • x = s (κ a) * x
        exact Algebra.smul_def (κ a) x }
  let g : Nc →ₗ[A] Mc :=
    { toFun := (id : H → H)
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        change H at x
        change s (κ a) * x = (κ a) • x
        exact (Algebra.smul_def (κ a) x).symm }
  let e : Mc ≃ₗ[A] Nc := LinearEquiv.ofLinearMap f g (by ext x; rfl) (by ext x; rfl)
  exact e.toModuleIso

/-- 元の実δ完全化逐次H0は、C上の実PD H0の同じ制限加群と同型。 -/
def deltaAlgebraPerfectionPDNativeH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj ≅ M :=
  deltaAlgebraPerfectionCompletionRestrictionH0Iso E j d ≪≫
    (ModuleCat.restrictScalars κ).mapIso
      (_root_.SerrePositivity.DerivedCompletion.iteratedPDH0LinearEquiv C (κ (p : A)) (κ d) p (map_natCast κ p)).toModuleIso

/-- 元の実δ完全化逐次H0を、標準合成係数射A→C→PDの加群と同定する。 -/
def deltaAlgebraPerfectionPDH0Iso :
    letI := pdCompletionCommRing C p (κ d)
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj (X).obj ≅
      baseChangeScalarModule t := by
  let := pdCompletionCommRing C p (κ d)
  exact deltaAlgebraPerfectionPDNativeH0Iso E j d ≪≫ deltaAlgebraPerfectionPDNativeModuleIso E j d

end SerrePositivity.BhattScholze

end DeltaAlgebraPerfectionPDH0Comparison

/-! ## 実δ完全化後のPD環の完全忠実平坦性 -/

@[expose] public noncomputable section PerfectPrismDeltaAlgebraPDCompletelyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DerivedCompletion
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "d" => OrientedPrism.generator P
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor M)
include hP hj hzero hFF

/-- 同じ実δ完全化逐次対象は、元の標準係数射を持つ実PD環のsingleと同型。 -/
def perfectPrismDeltaAlgebraPDSingleIso :
    letI := pdCompletionCommRing C p (κ d)
    X ≅ boundedAboveDerivedSingleFunctor.obj M := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.isoMk _
    (perfectPrismDeltaAlgebraCompletionSingleIso P E j hP hj hzero hFF ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (deltaAlgebraPerfectionPDH0Iso E j d))

/-- 同じ標準PD係数作用での(p,d)実還元の非零次数は零。 -/
theorem perfectPrismDeltaAlgebraPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing C p (κ d)
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing C p (κ d)
  obtain ⟨_, _, hz, _⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  exact (hz i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (perfectPrismDeltaAlgebraPDSingleIso P E j hP hj hzero hFF)))).symm

/-- 同じ標準PD係数作用での実還元H0は忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing C p (κ d)
  obtain ⟨_, _, _, hf⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj) := hf
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (perfectPrismDeltaAlgebraPDSingleIso P E j hP hj hzero hFF)))).toLinearEquiv.symm

/-- 同じ標準PD係数加群は、元の(p,d)係数拡大に関してTor非輪状。 -/
theorem perfectPrismDeltaAlgebraPD_torVanishing :
    letI := pdCompletionCommRing C p (κ d)
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing C p (κ d)
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismDeltaAlgebraPD_reduction_homology_isZero
    P E j hP hj hzero hFF (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 同じPD係数加群の通常剰余係数拡大は忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing C p (κ d)
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat P E j hP hj hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 実δ完全化後のPD環は、その標準A係数作用で(p,d)完全忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := pdCompletionCommRing C p (κ d)
  let Mc : ModuleCat.{u} A := M
  have hf : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P E j hP hj hzero hFF
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismDeltaAlgebraPD_torVanishing P E j hP hj hzero hFF) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze

end PerfectPrismDeltaAlgebraPDCompletelyFlat
