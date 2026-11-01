module
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness

/-! # 左準同型による導来tensor自然変換の可逆性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma moduleProjectiveTensorLeftMap_isIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    IsIso (DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D g).app
      ((moduleToHomotopy A D).obj M))) := by
  rw [BalancedTensor.rightTensorHomotopyLeftMap_app]
  let f := BalancedTensor.map A D (𝟙 M) g
  have hf : QuasiIso f := moduleHomotopicallyProjective_preserves_leftQuasiIso A D hM g hg
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} A) f).2 hf
  have he := NatIso.naturality_2 (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) f
  change IsIso (( _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) ⋙
    DerivedCategory.Qh).map f)
  rw [← he]
  infer_instance

lemma moduleResolutionDerivedTensorLeftFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (leftModuleQuasiIso A D).IsInvertedBy (moduleResolutionDerivedTensorLeftFunctor A D R) := by
  intro L L' g hg
  let τ : BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⋙
      DerivedCategory.Qh ⟶
    BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') ⋙
      DerivedCategory.Qh := Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D g)
    DerivedCategory.Qh
  change IsIso (Functor.whiskerLeft (moduleDerivedResolutionFunctor A D R) τ)
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (moduleToDerived A D) X
  let eR : (moduleDerivedResolutionFunctor A D R).obj X ≅
      (moduleToHomotopy A D).obj (R M).obj :=
    (moduleDerivedResolutionFunctor A D R).mapIso e.symm ≪≫
      moduleDerivedResolutionComputation A D R M
  change IsIso (τ.app ((moduleDerivedResolutionFunctor A D R).obj X))
  rw [NatTrans.isIso_app_iff_of_iso τ eR]
  exact moduleProjectiveTensorLeftMap_isIso A D (R M).projective g hg

lemma moduleDerivedTensorLeftFunctor_inverts :
    (leftModuleQuasiIso A D).IsInvertedBy (moduleDerivedTensorLeftFunctor A D) :=
  moduleResolutionDerivedTensorLeftFunctor_inverts A D (moduleCanonicalProjectiveResolution A D)

end SerrePositivity.DifferentialGraded
