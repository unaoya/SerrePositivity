module

public import SerrePositivity.AlgebraicGeometry.AffineQuasicoherentStandardCech
public import SerrePositivity.AlgebraicGeometry.CechAdditiveCoefficientComparison
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolution
public import SerrePositivity.AlgebraicGeometry.SchemeOpenCoverCechIntersections

/-!
概要：準連接層のアフィン座標上の標準開 Čech 計算を、元のスキームへ戻す。
方針：開埋め込みの制限の切断の同型を加法的係数比較に用いる。
規約：大域の係数環とアフィン座標環は同一視しない。
使われ方：有限標準細分による、任意のアフィン被覆の Čech 完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} (M : Y.Modules)

/-- 構造層加群の切断を、大域の係数環上の前層として扱う。 -/
def schemeModuleCechPresheaf : (Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
  ((SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop)).obj M).obj

variable {A : CommRingCat.{u}} (φ : Spec A ⟶ Y) [IsOpenImmersion φ]
variable {ι : Type} [LinearOrder ι] (U : ι → Y.Opens)

/-- アフィン開埋め込みの座標の切断と、元のスキームの切断の加法群の同型。 -/
def schemeModuleAffineCechCoefficientEquiv (T : Finset ι) :
    (openCoverCechDiagram (modulesSpecToSheaf.obj (M.restrict φ)).obj
      (fun i ↦ φ ⁻¹ᵁ U i)).obj T ≃+
    (openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) φ.opensRange) U).obj T :=
  ((M.restrictAppIso φ _ ) ≪≫ M.presheaf.mapIso
    (eqToIso (congrArg op (cechOpenIntersection_scheme_image_preimage φ U T)))).addCommGroupIsoToAddEquiv

/-- アフィン座標との加法的比較は、交叉を狭める制限に自然。 -/
theorem schemeModuleAffineCechCoefficientEquiv_naturality
    {T S : Finset ι} (h : T ⊆ S)
    (x : (openCoverCechDiagram (modulesSpecToSheaf.obj (M.restrict φ)).obj
      (fun i ↦ φ ⁻¹ᵁ U i)).obj T) :
    schemeModuleAffineCechCoefficientEquiv M φ U S
        (((openCoverCechDiagram (modulesSpecToSheaf.obj (M.restrict φ)).obj
          (fun i ↦ φ ⁻¹ᵁ U i)).map (homOfLE h)).hom x) =
      ((openCoverCechDiagram
        (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) φ.opensRange) U).map
          (homOfLE h)).hom (schemeModuleAffineCechCoefficientEquiv M φ U T x) := by
  change (M.presheaf.map _ ≫ M.presheaf.map _).hom x =
    (M.presheaf.map _ ≫ M.presheaf.map _).hom x
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

section Quasicoherent
variable [M.IsQuasicoherent] [Fintype ι]
variable (W : Y.Opens) (hW : IsAffineOpen W) (f : ι → Γ(Y, W))

include hW in
/-- アフィン開集合の標準開被覆上の、準連接層の増大 Čech 完全性。
原典 Stacks 30.2.1 の Hⁱ の消滅に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeModuleStandardOpenCech_exact (hspan : Ideal.span (Set.range f) = ⊤) (k : ℕ) :
    Function.Exact
      (fullCechDifferential (openCoverCechDiagram
        (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W)
          (fun i ↦ Y.basicOpen (f i))) k)
      (fullCechDifferential (openCoverCechDiagram
        (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W)
          (fun i ↦ Y.basicOpen (f i))) (k + 1)) := by
  let ψ := hW.fromSpec
  let N := M.restrict ψ
  let V := fun i ↦ Y.basicOpen (f i)
  let D := openCoverCechDiagram (modulesSpecToSheaf.obj N).obj (fun i ↦ ψ ⁻¹ᵁ V i)
  let E := openCoverCechDiagram
    (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) ψ.opensRange) V
  have hD : Function.Exact (fullCechDifferential D k) (fullCechDifferential D (k + 1)) := by
    have he : (fun i ↦ ψ ⁻¹ᵁ V i) = (fun i ↦ PrimeSpectrum.basicOpen (f i)) :=
      funext fun i ↦ hW.fromSpec_preimage_basicOpen (f i)
    have eD : D = openCoverCechDiagram (modulesSpecToSheaf.obj N).obj
        (fun i ↦ PrimeSpectrum.basicOpen (f i)) :=
      congrArg (openCoverCechDiagram (modulesSpecToSheaf.obj N).obj) he
    exact fullCechCoefficientEquiv_exact (eqToIso eD).symm k
      (specQuasicoherentStandardOpenCech_exact Γ(Y, W) N f hspan k)
  have hE := fullCechAdditiveCoefficientEquiv_exact D E
    (schemeModuleAffineCechCoefficientEquiv M ψ V)
    (fun h x ↦ schemeModuleAffineCechCoefficientEquiv_naturality M ψ V h x) k hD
  have eE : E = openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W) V :=
    congrArg (fun Z ↦ openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) Z) V) hW.opensRange_fromSpec
  exact fullCechCoefficientEquiv_exact (eqToIso eE) k hE

include hW in
/-- アフィン開集合の標準開被覆における、準連接層の増大項の単射性。 -/
theorem schemeModuleStandardOpenCech_zero_injective
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (fullCechDifferential (openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W)
        (fun i ↦ Y.basicOpen (f i))) 0) := by
  let ψ := hW.fromSpec
  let N := M.restrict ψ
  let V := fun i ↦ Y.basicOpen (f i)
  let D := openCoverCechDiagram (modulesSpecToSheaf.obj N).obj (fun i ↦ ψ ⁻¹ᵁ V i)
  let E := openCoverCechDiagram
    (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) ψ.opensRange) V
  have hD : Function.Injective (fullCechDifferential D 0) := by
    have he : (fun i ↦ ψ ⁻¹ᵁ V i) = (fun i ↦ PrimeSpectrum.basicOpen (f i)) :=
      funext fun i ↦ hW.fromSpec_preimage_basicOpen (f i)
    have eD : D = openCoverCechDiagram (modulesSpecToSheaf.obj N).obj
        (fun i ↦ PrimeSpectrum.basicOpen (f i)) :=
      congrArg (openCoverCechDiagram (modulesSpecToSheaf.obj N).obj) he
    exact fullCechCoefficientEquiv_zero_injective (eqToIso eD).symm
      (specQuasicoherentStandardOpenCech_zero_injective Γ(Y, W) N f hspan)
  have hE := fullCechAdditiveCoefficientEquiv_zero_injective D E
    (schemeModuleAffineCechCoefficientEquiv M ψ V)
    (fun h x ↦ schemeModuleAffineCechCoefficientEquiv_naturality M ψ V h x) hD
  have eE : E = openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) W) V :=
    congrArg (fun Z ↦ openCoverCechDiagram
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) Z) V) hW.opensRange_fromSpec
  exact fullCechCoefficientEquiv_zero_injective (eqToIso eE) hE

end Quasicoherent
end SerrePositivity.AlgebraicGeometry
