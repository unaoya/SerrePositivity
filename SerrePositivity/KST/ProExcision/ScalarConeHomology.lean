module

public import SerrePositivity.KST.ProExcision.PowerKernel
public import SerrePositivity.HomologicalAlgebra.ConeLES

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# スカラー cone のホモロジー比較

概要：Hⁱ(K)/aHⁱ(K) から Hⁱ(Cone(a,K)) への標準単射を構成する。
方針：cone 長完全列の中央の完全性で商へ降ろし、次の完全性で余りを測る。
規約：有界性・平坦性・有限性はこの段階では不要。
使われ方：KST Lemma 4.10。原典のスペクトル系列に代えて長完全列を使う。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 概要：a 倍によるホモロジーの商。
方針：スカラー線形写像の像で割る。
規約：通常の加群の商。使われ方：KST Lemma 4.10 の比較射の始域。 -/
def scalarHomologyQuotient (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ModuleCat.{u} R :=
  ModuleCat.of R (K.homology i ⧸ (a • (LinearMap.id : K.homology i →ₗ[R] K.homology i)).range)

/-- 概要：ホモロジーからその a 倍商への全射。
方針：部分加群の標準商写像を使う。
規約：a=0 も許す。使われ方：KST Lemma 4.10 の標準射の計算。 -/
def scalarHomologyQuotientπ (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    K.homology i ⟶ scalarHomologyQuotient a K i :=
  ModuleCat.ofHom (a • (LinearMap.id : K.homology i →ₗ[R] K.homology i)).range.mkQ

/-- 概要：a 倍は cone へのホモロジー写像で零となる。
方針：cone 長完全列の連続する二射の合成の零性を使う。
規約：複体上のスカラーとホモロジー上のスカラーを同定。
使われ方：KST Lemma 4.10 の比較射の商への降下。 -/
theorem scalarCone_inr_smul_zero (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (x : K.homology i) :
    (homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i).hom (a • x) = 0 := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Cone.exact₂ (smulId a K) i)
  have hh := (hex _).mpr ⟨x, rfl⟩
  change (homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i).hom
    ((homologyMap (smulId a K) i).hom x) = 0 at hh
  simpa only [smulId, homologyMap_smul, homologyMap_id,
    ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] using hh

/-- 概要：a 倍商からスカラー cone のホモロジーへの標準比較射。
方針：cone への包含が誘導する射を通常商へ降ろす。
規約：正則性は要求しない。使われ方：KST Lemma 4.10 の一変数段階。 -/
def scalarConeHomologyComparison (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    scalarHomologyQuotient a K i ⟶ ((scalarConeFunctor a).obj K).homology i :=
  ModuleCat.ofHom ((a • (LinearMap.id : K.homology i →ₗ[R] K.homology i)).range.liftQ
    (homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i).hom (by
      rintro _ ⟨x, rfl⟩
      exact scalarCone_inr_smul_zero a K i x))

/-- 概要：比較射と通常商写像の合成は cone への包含が誘導する射。
方針：商への降下の計算則を使う。
規約：射の等式で記述。使われ方：KST Lemma 4.10 の自然性。 -/
@[reassoc] theorem scalarConeHomologyComparison_π
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    scalarHomologyQuotientπ a K i ≫ scalarConeHomologyComparison a K i =
      homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i := by
  rfl

/-- 概要：通常商から cone ホモロジーへの標準射は単射。
方針：cone 長完全列の完全性で核の元を a 倍の像へ戻す。
規約：a の零因子性を許す。使われ方：KST Lemma 4.10 の pro 単射側。 -/
theorem scalarConeHomologyComparison_injective
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Injective (scalarConeHomologyComparison a K i).hom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (a • (LinearMap.id : K.homology i →ₗ[R] K.homology i)).range y
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (Cone.exact₂ (smulId a K) i)
  obtain ⟨z, hz⟩ := (hex x).mp hy
  refine ⟨z, ?_⟩
  change (homologyMap (smulId a K) i).hom z = x at hz
  simpa only [smulId, homologyMap_smul, homologyMap_id,
    ModuleCat.hom_smul, ModuleCat.hom_id] using hz

/-- 概要：比較射の像は cone 連結写像の核である。
方針：長完全列の完全性で持ち上げ、通常商へ射影する。
規約：i の次は i+1。使われ方：KST Lemma 4.10 の pro 全射側。 -/
theorem scalarConeHomologyComparison_exact
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Exact (scalarConeHomologyComparison a K i).hom
      (Cone.δ (smulId a K) i (i + 1) rfl).hom := by
  intro y
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Cone.exact₃ (smulId a K) i (i + 1) rfl)
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hex y).mp hy
    exact ⟨(scalarHomologyQuotientπ a K i).hom x, hx⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
      (a • (LinearMap.id : K.homology i →ₗ[R] K.homology i)).range x
    exact (hex _).mpr ⟨z, rfl⟩

/-- 概要：cone の連結写像の像は次次数の a 倍の核に含まれる。
方針：cone 長完全列の次の二射の合成を評価する。
規約：次数の一様な有限性は不要。使われ方：KST Lemma 4.10 の冪核への帰着。 -/
theorem scalarCone_connecting_smul_zero
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (x : ((scalarConeFunctor a).obj K).homology i) :
    a • (Cone.δ (smulId a K) i (i + 1) rfl).hom x = 0 := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Cone.exact₁ (smulId a K) i (i + 1) rfl)
  have hh := (hex _).mpr ⟨x, rfl⟩
  change (homologyMap (smulId a K) (i + 1)).hom
    ((Cone.δ (smulId a K) i (i + 1) rfl).hom x) = 0 at hh
  simpa only [smulId, homologyMap_smul, homologyMap_id,
    ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] using hh

end SerrePositivity.KST.ProExcision
