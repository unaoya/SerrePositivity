module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionAugmentation

/-! # 恒等kernelの作用比較と通常tensor増大

## 概要
恒等作用の既存比較を、通常の対角tensor単位子と解像度増大へ接続する。

## 方針
H⁰への単位子の降下と主導来局所化での計算を明示し、比較の選択を保つ。

## 規約と注意
局所Hom K-flat性を仮定しない。公開kernelIdentityIsoの定義を変更しない。

## 使われ方
U16aの合成比較と恒等比較の単位coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- H⁰に降ろした恒等比較の通常入力での成分。 -/
lemma kernelIdentityHomotopyIso_hom_app (M : ModuleCategory A D) :
    (kernelIdentityHomotopyIso A D).hom.app ((moduleToHomotopy A D).obj M) =
      (eqToIso (congrArg (fun G => G.obj M)
        (kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy_fac)).hom ≫
      (moduleToHomotopy A D).map ((kernelIdentityClosedIso A D).hom.app M) := by
  simp only [kernelIdentityHomotopyIso, Quotient.natIsoLift_hom, Quotient.natTransLift_app,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    eqToIso.hom, eqToHom_app]
  erw [Category.comp_id, Category.comp_id]

/-- H⁰恒等比較は元の通常単位子の主導来像を計算する。 -/
lemma kernelIdentityHomotopyIso_computation (M : ModuleCategory A D) :
    (kernelTensorHomotopyComputation A D D (Bimodule.diagonal A D) M).hom ≫
      (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app M) =
    (moduleHomotopyToDerivedClosed A D).map
        ((kernelIdentityHomotopyIso A D).hom.app ((moduleToHomotopy A D).obj M)) ≫
      (moduleToHomotopyDerivedIso A D).hom.app M := by
  have hn := (moduleToHomotopyDerivedIso A D).hom.naturality
    ((kernelIdentityClosedIso A D).hom.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc]
  erw [← hn]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [kernelIdentityHomotopyIso_hom_app]
  rfl

/-- 入力解像度の導来余単位は、通常入力で増大射そのものを計算する。 -/
lemma kernelInputResolutionDerivedCounitIso_hom_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelInputResolutionDerivedCounitIso A D R).hom.app ((moduleToDerived A D).obj M) =
      (moduleHomotopyToDerivedClosed A D).map
          ((moduleDerivedResolutionFunctor_fac A D R).hom.app M) ≫
        (moduleHomotopyToDerivedClosed A D).map ((moduleToHomotopy A D).map (R M).π) ≫
          (moduleToHomotopyDerivedIso A D).hom.app M := by
  simp only [kernelInputResolutionDerivedCounitIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, whiskerRight_app,
    kernelInputResolutionDerivedAugmentationIso, asIso_hom]
  erw [Category.id_comp, Category.comp_id, Category.id_comp]
  rfl

/-- 導来恒等比較は標準解像度上の通常単位子と入力増大を計算する。 -/
lemma kernelDerivedTensorOnBimoduleIdentityIso_model (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M) =
      (kernelResolutionDerivedTensorComputation A D D (Bimodule.diagonal A D)
        (moduleCanonicalProjectiveResolution A D) M).hom ≫
      (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app
        (moduleCanonicalProjectiveResolution A D M).obj) ≫
      (moduleToDerived A D).map (moduleCanonicalProjectiveResolution A D M).π := by
  let R := moduleCanonicalProjectiveResolution A D
  let Γ := (moduleDerivedResolutionFunctor_fac A D R).hom.app M
  let H := moduleHomotopyToDerivedClosed A D
  let τ := kernelIdentityHomotopyIso A D
  have hτ := τ.hom.naturality Γ
  simp only [Functor.id_map] at hτ
  have hτH : H.map (τ.hom.app ((moduleDerivedResolutionFunctor A D R).obj
        ((moduleToDerived A D).obj M))) ≫ H.map Γ =
      H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
        H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj)) := by
    have hh := congrArg H.map hτ
    simp only [H.map_comp] at hh
    exact hh.symm
  have hβ := (moduleToHomotopyDerivedIso A D).hom.naturality (R M).π
  simp only [Functor.comp_map] at hβ
  change (H.map (τ.hom.app _) ≫ 𝟙 _) ≫
    (kernelInputResolutionDerivedCounitIso A D R).hom.app ((moduleToDerived A D).obj M) = _
  rw [Category.comp_id, kernelInputResolutionDerivedCounitIso_hom_app]
  change H.map (τ.hom.app _) ≫ (H.map Γ ≫ H.map ((moduleToHomotopy A D).map (R M).π) ≫
      (moduleToHomotopyDerivedIso A D).hom.app M) =
    (((kernelHomotopyToDerived A D D (Bimodule.diagonal A D)).map Γ ≫
      (kernelTensorHomotopyComputation A D D (Bimodule.diagonal A D) (R M).obj).hom) ≫ _ ≫ _)
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [kernelIdentityHomotopyIso_computation]
  slice_rhs 3 4 => erw [← hβ]
  slice_lhs 1 2 => rw [hτH]
  change ((H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
    H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj))) ≫
    H.map ((moduleToHomotopy A D).map (R M).π)) ≫ (moduleToHomotopyDerivedIso A D).hom.app M =
    H.map ((kernelTensor A D D (Bimodule.diagonal A D)).onHomotopy.map Γ) ≫
      H.map (τ.hom.app ((moduleToHomotopy A D).obj (R M).obj)) ≫
      H.map ((moduleToHomotopy A D).map (R M).π) ≫ (moduleToHomotopyDerivedIso A D).hom.app M
  simp only [Category.assoc]

/-- 導来恒等比較は通常tensor増大と元の対角単位子を通る経路に一致する。 -/
lemma kernelDerivedTensorOnBimoduleIdentityIso_augmentation (M : ModuleCategory A D) :
    (kernelDerivedTensorOnBimoduleIdentityIso A D).hom.app ((moduleToDerived A D).obj M) =
      (kernelDerivedTensorAugmentation A D D (Bimodule.diagonal A D)).app M ≫
        (moduleToDerived A D).map ((kernelIdentityClosedIso A D).hom.app M) := by
  rw [kernelDerivedTensorOnBimoduleIdentityIso_model, kernelDerivedTensorAugmentation_app]
  have h := congrArg (moduleToDerived A D).map
    ((kernelIdentityClosedIso A D).hom.naturality (moduleCanonicalProjectiveResolution A D M).π)
  simp only [Functor.map_comp, Functor.id_map] at h
  simp only [Category.assoc]
  rw [h]

end SerrePositivity.DifferentialGraded.Morita
