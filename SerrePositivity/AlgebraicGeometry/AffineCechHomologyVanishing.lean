module

public import SerrePositivity.AlgebraicGeometry.SchemeCommonAffineCechScalarHomology
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComparison

/-!
概要：アフィンなスキームの有限アフィン被覆による、正次数の Čech H の消滅。
方針：全空間だけの被覆と共通細分で比較し、狭義増加複体の長さを使う。
規約：準連接係数と実際の被覆による Čech 版。
使われ方：中心外のアフィンな底変換での消滅を、台の制御に渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} [IsAffine Y]
variable {R : Type u} [CommRing R] (φ : R →+* Γ(Y, ⊤))
variable (M : Y.Modules) [M.IsQuasicoherent]
variable {ι : Type} [LinearOrder ι] [Fintype ι]
variable (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤)

include hU hcU in
/-- アフィンスキームの準連接係数は有限アフィン被覆の正次数 Čech H が消える。
BST13 Lemma 3.9 の台の議論で使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineSchemeCechHomology_isZero (q : ℕ) (hq : 0 < q) :
    IsZero ((fullCechComplex (openCoverCechDiagram
      (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U)).homology q) := by
  let V : Fin 1 → Y.Opens := fun _ ↦ ⊤
  let D := openCoverCechDiagram (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) V
  have e := schemeModuleCommonAffineCechScalarHomologyIso φ M U V hU
    (fun _ ↦ isAffineOpen_top Y) hcU (by simp [V]) q
  have hz : IsZero ((fullCechComplex D).homology q) :=
    (isZero_orderedCechHomology D q (by simpa using Nat.succ_le_of_lt hq)).of_iso (fullCechOrderedHomologyIso D q)
  exact hz.of_iso e

end SerrePositivity.AlgebraicGeometry
