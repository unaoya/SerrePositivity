module

public import SerrePositivity.AlgebraicGeometry.ReesIteratedClosedGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness

/-!
概要：一重の商 M/(JM+IⁿM) の次数成分は、実際の直和分解を与える。
方針：分母の和の斉次性を成分射影で示し、既存の商の内部直和を使う。
規約：Noether 性は Čech コホモロジーの有限性を述べる段階で使う。
使われ方：閉厚化の比較後の係数にも、次数分解と射影有限性を渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 分母 JM+IⁿM は、元の Proj 次数について斉次。 -/
theorem reesIteratedClosedSum_isHomogeneous (n : ℕ) :
    ((reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n).restrictScalars R).IsHomogeneous G := by
  let S := reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1
  let T := reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n
  have hS : (S.restrictScalars R).IsHomogeneous G :=
    reesAdicProjectiveSubmodule_isHomogeneous (ι := ι) J G 1
  have hT : (T.restrictScalars R).IsHomogeneous G :=
    reesAdicProjectiveSubmodule_isHomogeneous (ι := ι) I G n
  intro d x hx
  have hx' : x ∈ S.restrictScalars R ⊔ T.restrictScalars R := by
    change x ∈ (S ⊔ T).restrictScalars R at hx
    simpa only [Submodule.restrictScalars_sup] using hx
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx'
  have hs' := ((Submodule.IsHomogeneous.mem_iff G hS).mp hs) d
  have ht' := ((Submodule.IsHomogeneous.mem_iff G hT).mp ht) d
  change SerrePositivity.HilbertSerre.gradeProjection G d (s + t) ∈ (S ⊔ T).restrictScalars R
  rw [Submodule.restrictScalars_sup, map_add]
  exact Submodule.mem_sup.mpr ⟨SerrePositivity.HilbertSerre.gradeProjection G d s, hs',
    SerrePositivity.HilbertSerre.gradeProjection G d t, ht', rfl⟩

/-- 一重の商の Proj 次数成分は、商加群の直和分解を与える。 -/
@[instance_reducible]
def reesIteratedClosedSumPieceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesIteratedClosedSumPiece (ι := ι) I J G n) :=
  (SerrePositivity.HilbertSerre.isInternal_quotientGrade G
    ((reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) J 1 ⊔
      reesAdicProjectivePolynomialSubmodule (ι := ι) (M := M) I n).restrictScalars R)
    (reesIteratedClosedSum_isHomogeneous (ι := ι) I J G n)).chooseDecomposition

local instance closedSumDecompositionGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) :=
  reesIteratedClosedSumPieceGradedSMul (ι := ι) I J G n

variable [LinearOrder ι] [Fintype ι] [IsNoetherianRing R]
variable [Module.Finite (MvPolynomial ι R) M]

/-- 一重の商 M/(JM+IⁿM) の標準開 Čech コホモロジーは有限生成。
原典 Stacks 30.19.2 の Hⁱ の射影有限性に対応する、閉厚化の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesIteratedClosedSumCechHomology_finite (n : ℕ) (d : ℤ) (q : ℕ) :
    Module.Finite R ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) d)).homology q) := by
  letI := reesIteratedClosedSumPieceDecomposition (ι := ι) I J G n
  exact projectiveNatGradedFullCechHomology_finite (ι := ι)
    (reesIteratedClosedSumPiece (ι := ι) I J G n) d q

end SerrePositivity.AlgebraicGeometry
