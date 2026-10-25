module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionSourceTensor
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionSourceTensorDelta

/-! # 実通常テンソルのδ構造と両因子の標準包含

raw包のδ切断を標準比較同型とW₂写像で引き戻す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (y : A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => TensorProduct P₀ A P₀
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀

/-- 実通常テンソル上の、raw包の標準比較で引き戻した具体的δ構造。 -/
def deltaPDivisionSourceTensorDelta :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    DeltaStructure p R₀ := by
  exact deltaDivisionSourceTensorDelta D (p : A) a₀

/-- 実通常テンソルからraw包への標準環同型はδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaPDivisionSourceTensorDelta (σ := σ) D y).IsDeltaHom
      (deltaAdjoinDivisionStructure D (p : A) a₀)
      (deltaPDivisionSourceTensorEquiv D y).toRingHom := by
  exact deltaDivisionSourceTensorEquiv_isDeltaHom D (p : A) a₀

/-- raw包から実通常テンソルへの標準逆同型もδ構造を保存する。 -/
theorem deltaPDivisionSourceTensorEquiv_symm_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (deltaAdjoinDivisionStructure D (p : A) a₀).IsDeltaHom
      (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      (deltaPDivisionSourceTensorEquiv D y).symm.toRingHom := by
  exact deltaDivisionSourceTensorEquiv_symm_isDeltaHom D (p : A) a₀

/-- 通常テンソルの元の基底Aの標準包含はδ射。 -/
theorem deltaPDivisionSourceTensor_includeLeft_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    D.IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeLeftRingHom := by
  exact deltaDivisionSourceTensor_includeLeft_isDeltaHom D (p : A) a₀

/-- 通常テンソルの終域自由δ環Lの標準包含もδ射。 -/
theorem deltaPDivisionSourceTensor_includeRight_isDeltaHom :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    (relativeFreeDeltaStructure σ D).IsDeltaHom (deltaPDivisionSourceTensorDelta (σ := σ) D y)
      Algebra.TensorProduct.includeRight.toRingHom := by
  exact deltaDivisionSourceTensor_includeRight_isDeltaHom D (p : A) a₀

/-- 両因子の標準包含をδ射にするδ構造は、構成したものに一意に一致する。 -/
theorem deltaPDivisionSourceTensorDelta_unique :
    letI := deltaDivisionSourceEvalAlgebra (σ := σ) D y
    letI := deltaPDivisionSourceTargetAlgebra (σ := σ) D
    letI : Module P₀ P₀ := Algebra.toModule
    ∀ E : DeltaStructure p R₀,
      D.IsDeltaHom E Algebra.TensorProduct.includeLeftRingHom →
      (relativeFreeDeltaStructure σ D).IsDeltaHom E Algebra.TensorProduct.includeRight.toRingHom →
      E = deltaPDivisionSourceTensorDelta (σ := σ) D y := by
  exact deltaDivisionSourceTensorDelta_unique D (p : A) a₀


end SerrePositivity.BhattScholze
