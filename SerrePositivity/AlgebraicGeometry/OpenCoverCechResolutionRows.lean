module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolution
public import SerrePositivity.AlgebraicGeometry.CechCoefficientExactness
public import SerrePositivity.AlgebraicGeometry.CechProductCoefficients
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechSplitIntersection

/-!
概要：二重 Čech の正次数の行を、交叉上での Čech の直積として扱う。
方針：二つの交叉の順序を自然に交換し、各交叉を含む頂点で縮約する。
規約：行の完全性には準連接性を要せず、細分の包含だけを用いる。
使われ方：有限標準細分と一般の共通細分に B1 を適用するための行の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat R) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Opens X) (V : κ → Opens X)

/-- 二重 Čech の一つの行の係数を、交叉上の係数図式の直積として表示する。 -/
def openCoverCechResolutionRowIso (j : ℕ) :
    openCoverCechDiagram (openCoverCechResolution P V j) U ≅
      fullCechProductCoefficientDiagram (fun s : Fin j → κ ↦
        openCoverCechDiagram (openCoverIntersectionPresheaf P
          (cechOpenIntersection V (cechTupleSupport s))) U) :=
  NatIso.ofComponents (fun T ↦
    (LinearEquiv.piCongrRight (fun s : Fin j → κ ↦
      (P.mapIso (eqToIso (congrArg op (inf_comm
        (cechOpenIntersection U T) (cechOpenIntersection V (cechTupleSupport s)))))).toLinearEquiv)).toModuleIso) (by
      intro T S h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext s
      change (P.map _ ≫ P.map _).hom (x s) = (P.map _ ≫ P.map _).hom (x s)
      rw [← P.map_comp, ← P.map_comp]
      congr 2)

/-- 正長の交叉は、その中に現れる任意の一つの被覆開に含まれる。 -/
theorem cechOpenIntersection_le_tuple_member {j : ℕ} (s : Fin j → κ) (i : Fin j) :
    cechOpenIntersection V (cechTupleSupport s) ≤ V (s i) :=
  iInf_le_of_le (s i) (iInf_le_of_le
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) le_rfl)

/-- 細分である二重 Čech の正次数の行では、増大項からの微分は単射。 -/
theorem openCoverCechResolutionRow_zero_injective
    (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i)) (j : ℕ) (hj : 0 < j) :
    Function.Injective
      (fullCechDifferential (openCoverCechDiagram (openCoverCechResolution P V j) U) 0) := by
  apply fullCechCoefficientEquiv_zero_injective (openCoverCechResolutionRowIso P U V j).symm
  apply fullCechProduct_zero_injective
  intro s
  exact openCoverCechSplitIntersection_zero_injective P _ U (ρ (s ⟨0, hj⟩))
    ((cechOpenIntersection_le_tuple_member V s ⟨0, hj⟩).trans (hρ _))

/-- 細分である二重 Čech の正次数の行は、増大 Čech として完全。 -/
theorem openCoverCechResolutionRow_exact
    (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i)) (j : ℕ) (hj : 0 < j) (k : ℕ) :
    Function.Exact
      (fullCechDifferential (openCoverCechDiagram (openCoverCechResolution P V j) U) k)
      (fullCechDifferential (openCoverCechDiagram (openCoverCechResolution P V j) U) (k + 1)) := by
  apply fullCechCoefficientEquiv_exact (openCoverCechResolutionRowIso P U V j).symm k
  apply fullCechProduct_exact
  intro s
  exact openCoverCechSplitIntersection_exact P _ U (ρ (s ⟨0, hj⟩))
    ((cechOpenIntersection_le_tuple_member V s ⟨0, hj⟩).trans (hρ _)) k

end SerrePositivity.AlgebraicGeometry
