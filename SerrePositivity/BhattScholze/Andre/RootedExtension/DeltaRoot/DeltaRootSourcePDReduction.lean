module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceCoefficientSquare

/-! # 元の(p,d)係数商への実根添加導来還元

拡張イデアルと降下係数射を照合し、二つの実導来還元の比較を具体的な型へ特殊化する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "C₀" => algebraMap A L₀
variable (d : A)
local notation "I₀" => Ideal.span {(p : A), d}
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d

omit [Fact p.Prime] in
/-- 元の(p,d)の二重係数包含に沿う拡張は、実源の(p,C(Cd))に一致する。 -/
theorem deltaRootSourcePDIdeal_map : Ideal.map C₀ I₀ = K₀ := by
  rw [Ideal.map_span]
  simp only [Set.image_pair, map_natCast]
  rfl

/-- 任意の実源上の実導来対象について、元の(p,d)還元と実源商での還元を結ぶ。 -/
def deltaRootSourcePDDerivedSquareIso
    (X : DerivedCategory.Minus (ModuleCat.{u} L₀)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  let F (J : Ideal L₀) :=
    Σ' h : I₀ ≤ J.comap C₀,
      letI := Ideal.Quotient.algebraQuotientOfLEComap h
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
          ((boundedAboveDerivedRestrictScalars C₀).obj X) ≅
        (boundedAboveDerivedRestrictScalars (algebraMap (A ⧸ I₀) (L₀ ⧸ J))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk J)).obj X)
  let e : F ((I₀).map C₀) :=
    ⟨Ideal.le_comap_map, deltaRootSourceCoefficientDerivedSquareIso I₀ X P⟩
  let e' : F K₀ := Eq.mp (congrArg F (deltaRootSourcePDIdeal_map (σ := σ) (p := p) d)) e
  letI := Ideal.Quotient.algebraQuotientOfLEComap e'.1
  have hκ : algebraMap (A ⧸ I₀) (L₀ ⧸ K₀) = κ₀ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro a
    rfl
  have he := e'.2
  simpa only [hκ] using he

variable [Unique σ] (D : DeltaStructure p A) (b : σ → A)
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

/-- 実根添加二因子導来対象の、元の係数環Aへの実制限対象。 -/
abbrev DeltaRootSourceCoefficientObject :=
  (boundedAboveDerivedRestrictScalars C₀).obj X₀

set_option maxHeartbeats 800000 in
-- 二つの実係数作用を持つテンソルモデルと既存還元対象の型を同時に照合するため。
/-- 元のA/(p,d)での実導来還元と、既存の実源商上の根添加還元の比較。 -/
def deltaRootSourceCoefficientPDReductionIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        (DeltaRootSourceCoefficientObject d D b) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj (DeltaRootSourceQuotientDerived D d b) :=
  deltaRootSourcePDDerivedSquareIso (p := p) (A := A) (σ := σ) d X₀
    (boundedAboveDerivedTensorModel
      (boundedAboveDerivedSingleFunctor.obj Mβ) (boundedAboveDerivedSingleFunctor.obj Mα))

end SerrePositivity.BhattScholze
