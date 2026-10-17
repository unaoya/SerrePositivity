module
public import SerrePositivity.DifferentialGraded.Morita.KernelTensor
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence

/-! # U16aの通常graph作用と既存導来延長の計算モデル

主導来kernel作用の実装前にも、任意射影解像度での通常graph計算を公開する。
主導来kernel作用との全射自然な同型はそのAPIの実装後に別途接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def quasiEquivalenceGraphResolutionComputation {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj
        ((kernelTensor A D E (functorGraph A D E F)).onClosed.obj R.obj) := by
  rw [kernelTensor_graph]
  exact dgDerivedExtensionResolutionComputation A D E F R

lemma quasiEquivalenceGraphResolution_perfect {M : ModuleCategory A D}
    (hM : modulePerfect A D ((moduleToDerived A D).obj M))
    (R : ModuleProjectiveResolution A D M) :
    modulePerfect A E ((moduleToDerived A E).obj
      ((kernelTensor A D E (functorGraph A D E F)).onClosed.obj R.obj)) :=
  (modulePerfect A E).prop_of_iso (quasiEquivalenceGraphResolutionComputation A D E F R)
    (dgDerivedExtension_perfect A D E F hM)

end SerrePositivity.DifferentialGraded.Morita
