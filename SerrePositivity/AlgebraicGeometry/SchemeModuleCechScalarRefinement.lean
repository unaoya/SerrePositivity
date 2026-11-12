module

public import SerrePositivity.AlgebraicGeometry.SchemeModuleCechRefinement
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechScalarRestriction

/-!
概要：準連接層の Čech の細分比較を、任意の基底環の作用に制限する。
方針：各アフィン交叉で係数制限後も増大 Čech が完全なことを、実際の cone に渡す。
規約：基底環から大域切断の環への環準同型を指定する。
使われ方：射影標準開で計算した元の基底環上の Čech H と共通細分を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {R : Type u} [CommRing R] (φ : R →+* Γ(Y, ⊤))
variable (M : Y.Modules) [M.IsQuasicoherent]
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)

/-- 準連接層のアフィン被覆の細分比較は、任意の基底環の作用に制限しても同型。
原典 Stacks 30.2.6 のアフィン被覆の比較の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeModuleCechScalarRefinement_homologyMap_isIso
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcover : (⨆ j, V j) = ⊤) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (openCoverCechRefinementMap (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ)
        U V ρ hρ) q) := by
  apply openCoverCechRefinement_homologyMap_isIso
    (schemeModuleCechPresheaf M ⋙ ModuleCat.restrictScalars φ) U V ρ hρ ?_ ?_ q
  · intro i t
    have hn : (cechTupleSupport t).Nonempty :=
      ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hW := cechOpenIntersection_isAffineOpen U hU _ hn
    apply openCoverCechAcyclic_restrictScalars φ
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) _) V
    apply schemeModuleAffineOpenCech_acyclic M _ hW V
    · intro j
      exact hW.inf (hV j)
    · rw [hcover]
      exact le_top
  · intro i t
    have hn : (cechTupleSupport t).Nonempty :=
      ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hW := cechOpenIntersection_isAffineOpen V hV _ hn
    apply openCoverCechAcyclic_restrictScalars φ
      (openCoverIntersectionPresheaf (schemeModuleCechPresheaf M) _) V
    apply schemeModuleAffineOpenCech_acyclic M _ hW V
    · intro j
      exact hW.inf (hV j)
    · rw [hcover]
      exact le_top

end SerrePositivity.AlgebraicGeometry
