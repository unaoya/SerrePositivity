module

public import SerrePositivity.AlgebraicGeometry.AffineLocalizingCech

/-!
概要：Spec 上の準連接層について、標準開被覆の増大 Čech 完全性を得る。
方針：Mathlib の準連接層の大域切断からの tilde 同型を、局所化条件に変換する。
規約：原典の層コホモロジーとの比較は形式化しない Čech 版。
使われ方：共通アフィン細分の交叉上の準連接係数の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent]
variable {ι : Type} [LinearOrder ι] [Fintype ι] (f : ι → R)

/-- 準連接層の標準開への制限は、その元での局所化。 -/
theorem specQuasicoherent_isLocalizing :
    IsLocalizing (modulesSpecToSheaf.obj M) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance

/-- 準連接層の標準開被覆の増大項の単射性。 -/
theorem specQuasicoherentStandardOpenCech_zero_injective
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (fullCechDifferential
      (openCoverCechDiagram (modulesSpecToSheaf.obj M).obj
        (fun i ↦ PrimeSpectrum.basicOpen (f i))) 0) := by
  let P := (modulesSpecToSheaf.obj M).obj
  exact fullCechCoefficientEquiv_zero_injective (specStandardCechOpenDiagramIso P f)
    (specStandardCech_zero_injective P (specQuasicoherent_isLocalizing R M) f hspan)

/-- Spec 上の準連接層の標準開被覆の増大 Čech 完全性。
原典 Stacks 30.2.1 の Hⁱ の消滅に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem specQuasicoherentStandardOpenCech_exact
    (hspan : Ideal.span (Set.range f) = ⊤) (k : ℕ) :
    Function.Exact (fullCechDifferential
      (openCoverCechDiagram (modulesSpecToSheaf.obj M).obj
        (fun i ↦ PrimeSpectrum.basicOpen (f i))) k)
      (fullCechDifferential
        (openCoverCechDiagram (modulesSpecToSheaf.obj M).obj
          (fun i ↦ PrimeSpectrum.basicOpen (f i))) (k + 1)) :=
  specStandardOpenCech_exact (modulesSpecToSheaf.obj M).obj
    (specQuasicoherent_isLocalizing R M) f hspan k

end SerrePositivity.AlgebraicGeometry
