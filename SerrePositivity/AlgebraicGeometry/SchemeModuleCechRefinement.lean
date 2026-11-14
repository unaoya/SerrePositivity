module

public import SerrePositivity.AlgebraicGeometry.SchemeModuleAffineCoverCech
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechRefinementHomology

/-!
概要：準連接層のアフィン被覆の細分が、実際の Čech H の同型を誘導する。
方針：非空交叉のアフィン性とアフィン上の増大 Čech 完全性を、実際の cone の列へ渡す。
規約：係数は大域切断の環上。導来関手の層コホモロジーとの比較は形式化しない。
使われ方：共通アフィン細分による、射影 Čech 計算の被覆によらない比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {Y : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable (M : Y.Modules) [M.IsQuasicoherent]
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (U : ι → Y.Opens) (V : κ → Y.Opens)

/-- 準連接層のアフィン開被覆の細分は、各次数の Čech H の同型を誘導する。
原典 Stacks 30.2.6 のアフィン被覆の比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeModuleCechRefinement_homologyMap_isIso
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcover : (⨆ j, V j) = ⊤) (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (openCoverCechRefinementMap (schemeModuleCechPresheaf M) U V ρ hρ) q) := by
  apply openCoverCechRefinement_homologyMap_isIso (schemeModuleCechPresheaf M) U V ρ hρ ?_ ?_ q
  · intro i t
    have hn : (cechTupleSupport t).Nonempty :=
      ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hW := cechOpenIntersection_isAffineOpen U hU _ hn
    apply schemeModuleAffineOpenCech_acyclic M _ hW V
    · intro j
      exact hW.inf (hV j)
    · rw [hcover]
      exact le_top
  · intro i t
    have hn : (cechTupleSupport t).Nonempty :=
      ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hW := cechOpenIntersection_isAffineOpen V hV _ hn
    apply schemeModuleAffineOpenCech_acyclic M _ hW V
    · intro j
      exact hW.inf (hV j)
    · rw [hcover]
      exact le_top

end SerrePositivity.AlgebraicGeometry
