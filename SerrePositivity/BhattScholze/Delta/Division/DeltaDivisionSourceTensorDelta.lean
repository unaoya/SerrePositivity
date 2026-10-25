module

public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceTensor
public import SerrePositivity.BhattScholze.Delta.DeltaTransport

/-! # 実通常テンソルのδ構造と両因子の標準包含

raw包のδ切断を標準比較同型とW₂写像で引き戻す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => c
local notation "B₀" => DeltaAdjoinDivision D d a₀

/-- 実通常テンソル上の、raw包の標準比較で引き戻した具体的δ構造。 -/
def deltaDivisionSourceTensorDelta :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    DeltaStructure p R₀ := by
  letI := deltaDivisionSourceEvaluationAlgebra D c
  letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  letI : Module P₀ P₀ := Algebra.toModule
  let e := deltaDivisionSourceTensorEquiv (σ := σ) D d c
  let E := deltaAdjoinDivisionStructure D d a₀
  exact E.comapEquiv e

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem deltaDivisionSourceTensorEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaDivisionSourceTensorDelta (σ := σ) D d c).IsDeltaHom
      (deltaAdjoinDivisionStructure D d a₀)
      (deltaDivisionSourceTensorEquiv D d c).toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let e := deltaDivisionSourceTensorEquiv (σ := σ) D d c
  let E := deltaAdjoinDivisionStructure D d a₀
  exact E.comapEquiv_isDeltaHom e

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem deltaDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaAdjoinDivisionStructure D d a₀).IsDeltaHom
      (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      (deltaDivisionSourceTensorEquiv D d c).symm.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  exact (deltaDivisionSourceTensorEquiv_isDeltaHom (σ := σ) D d c).symm

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem deltaDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      Algebra.TensorProduct.includeLeftRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  have h := (deltaDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D d c).comp
    (deltaAdjoinDivisionMap_isDeltaHom D d a₀)
  change D.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
    ((deltaDivisionSourceRawToTensor D d c).comp (deltaAdjoinDivisionMap D d a₀)) at h
  rw [deltaDivisionSourceRawToTensor_comp_base] at h
  exact h

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem deltaDivisionSourceTensor_includeRight_isDeltaHom :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    (relativeFreeDeltaStructure σ D).IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
      Algebra.TensorProduct.includeRight.toRingHom := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  let E := relativeFreeDeltaStructure σ D
  let J := E.deltaClosure (deltaDivisionRelationIdeal d a₀)
  have hq := E.isDeltaHom_quotient_mk J (E.isStable_deltaClosure _)
  have h := (deltaDivisionSourceTensorEquiv_symm_isDeltaHom (σ := σ) D d c).comp hq
  change E.IsDeltaHom (deltaDivisionSourceTensorDelta (σ := σ) D d c)
    ((deltaDivisionSourceRawToTensor D d c).comp (Ideal.Quotient.mk J)) at h
  rw [deltaDivisionSourceRawToTensor_comp_quotient] at h
  exact h

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem deltaDivisionSourceTensorDelta_unique :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = deltaDivisionSourceTensorDelta (σ := σ) D d c := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  intro E hL hR
  let T := deltaDivisionSourceTensorDelta (σ := σ) D d c
  have hL' := deltaDivisionSourceTensor_includeLeft_isDeltaHom (σ := σ) D d c
  have hR' := deltaDivisionSourceTensor_includeRight_isDeltaHom (σ := σ) D d c
  have hLeft : E.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeLeftRingHom :=
    ((D.isDeltaHom_iff_sectionHom_comp E _).mp hL).symm.trans
      ((D.isDeltaHom_iff_sectionHom_comp T _).mp hL')
  have hRight : E.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      T.sectionHom.comp Algebra.TensorProduct.includeRight.toRingHom :=
    (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp E _).mp hR).symm.trans
      (((relativeFreeDeltaStructure σ D).isDeltaHom_iff_sectionHom_comp T _).mp hR')
  have hs : E.sectionHom = T.sectionHom := Algebra.TensorProduct.ringHom_ext hLeft hRight
  apply DeltaStructure.ext
  intro r
  exact congrArg (fun z : WittTwo p R₀ => z.coeff 1) (RingHom.congr_fun hs r)

/-- 可換な二環射の自由δ因子側がδ射なら、通常pushoutからの延長も一意なδ射。
係数側のδ両立性は自由δ係数射と可換性から従うため追加仮定しない。 -/
theorem existsUnique_deltaDivisionSourceTensorDeltaHom {T : Type w} [CommRing T]
    (F : DeltaStructure p T) (f : A →+* T) (g : P₀ →+* T)
    (hg : (relativeFreeDeltaStructure σ D).IsDeltaHom F g)
    (h : g.comp (deltaDivisionSourceMap D d) = f.comp (deltaDivisionSourceEval D a₀)) :
    letI := deltaDivisionSourceEvaluationAlgebra D c
    letI := deltaDivisionSourceTargetAlgebra (σ := σ) D d
    letI : Module P₀ P₀ := Algebra.toModule
    ∃! k : R₀ →+* T, (deltaDivisionSourceTensorDelta D d c).IsDeltaHom F k ∧
      k.comp Algebra.TensorProduct.includeLeftRingHom = f ∧
      k.comp Algebra.TensorProduct.includeRight.toRingHom = g := by
  let := deltaDivisionSourceEvaluationAlgebra D c
  let := deltaDivisionSourceTargetAlgebra (σ := σ) D d
  let : Module P₀ P₀ := Algebra.toModule
  obtain ⟨k, hk, _⟩ := existsUnique_deltaDivisionSourceRawLift D d c f g h
  let J := (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d c)
  let q := Ideal.Quotient.mk J
  have hq : (relativeFreeDeltaStructure σ D).IsDeltaHom
      (deltaAdjoinDivisionStructure D d c) q :=
    (relativeFreeDeltaStructure σ D).isDeltaHom_quotient_mk J
      ((relativeFreeDeltaStructure σ D).isStable_deltaClosure _)
  have hkdelta : (deltaAdjoinDivisionStructure D d c).IsDeltaHom F k := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change k ((deltaAdjoinDivisionStructure D d c).delta (q r)) = F.delta (k (q r))
    rw [← hq r]
    have hk₀ := DFunLike.congr_fun hk.1 r
    have hk₁ := DFunLike.congr_fun hk.1 ((relativeFreeDeltaStructure σ D).delta r)
    change k (q r) = g r at hk₀
    change k (q ((relativeFreeDeltaStructure σ D).delta r)) = _ at hk₁
    rw [hk₁, hk₀]
    exact hg r
  let e := deltaDivisionSourceTensorEquiv D d c
  let l := k.comp e.toRingHom
  have hl : l.comp Algebra.TensorProduct.includeLeftRingHom = f := by
    apply RingHom.ext
    intro x
    change k (e (x ⊗ₜ[P₀] 1)) = f x
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one]
    exact DFunLike.congr_fun hk.2 x
  have hr : l.comp Algebra.TensorProduct.includeRight.toRingHom = g := by
    apply RingHom.ext
    intro r
    change k (e (1 ⊗ₜ[P₀] r)) = g r
    rw [deltaDivisionSourceTensorEquiv_tmul, map_one, one_mul]
    exact DFunLike.congr_fun hk.1 r
  refine ⟨l, ⟨hkdelta.comp (deltaDivisionSourceTensorEquiv_isDeltaHom D d c), hl, hr⟩, ?_⟩
  intro z hz
  exact Algebra.TensorProduct.ringHom_ext (hz.2.1.trans hl.symm) (hz.2.2.trans hr.symm)

end SerrePositivity.BhattScholze
