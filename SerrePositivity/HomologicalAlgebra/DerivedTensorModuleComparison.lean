module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleModels
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleResolution

/-! # Compare the actual derived tensor with the established module and Tor functors -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual derived tensor with the left module in degree zero, restricted to modules. -/
def boundedAboveDerivedTensorModuleFunctor (M : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ((((Functor.const (ModuleCat R)).obj (boundedAboveDerivedSingleFunctor.obj M)).prod'
    boundedAboveDerivedSingleFunctor) ⋙ boundedAboveDerivedTensor) ⋙ DerivedCategory.Minus.ι

/-- The actual derived tensor agrees with the previous one-sided module construction. -/
def boundedAboveDerivedTensorModuleIso (M N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensorModuleFunctor M).obj N ≅ (realizedDerivedTensorFunctor R M).obj N :=
  derivedTensorModuleModelIso M N ≪≫
    DerivedCategory.Q.mapIso (cochainTensorSingleLeftIso M (extRes (projectiveResolution N))) ≪≫
    DerivedCategory.Q.mapIso (mapExtendIso (tensorLeft M) (projectiveResolution N).complex embUp) ≪≫
    (realizedDerivedTensorResolutionIso M (projectiveResolution N)).symm

/-- Compatibility with all maps of the right module. -/
lemma boundedAboveDerivedTensorModuleIso_naturality_right (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (boundedAboveDerivedTensorModuleFunctor M).map g ≫
        (boundedAboveDerivedTensorModuleIso M N').hom =
      (boundedAboveDerivedTensorModuleIso M N).hom ≫ (realizedDerivedTensorFunctor R M).map g := by
  let P := projectiveResolution N
  let Q := projectiveResolution N'
  have hm := derivedTensorModuleModelIso_naturality (𝟙 M) g
  simp only [CategoryTheory.Functor.map_id] at hm
  have hr := realizedDerivedTensorResolutionIso_naturality M g P Q
  apply (cancel_mono (realizedDerivedTensorResolutionIso M Q).hom).mp
  dsimp only [boundedAboveDerivedTensorModuleFunctor, P, Q] at *
  simp only [boundedAboveDerivedTensorModuleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M))
      (boundedAboveDerivedSingleFunctor.map g))).hom ≫
    (derivedTensorModuleModelIso M N').hom ≫ _ = _
  rw [← Category.assoc, hm, Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    cochainTensorSingleLeftIso_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map
    (mapExtendIso_naturality (tensorLeft M) embUp (ProjectiveResolution.lift g P Q))

/-- Compatibility with all maps of the unresolved left module. -/
lemma boundedAboveDerivedTensorModuleIso_naturality_left
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom ≫
        (boundedAboveDerivedTensorModuleIso M' N).hom =
      (boundedAboveDerivedTensorModuleIso M N).hom ≫ (realizedDerivedTensorMapLeft R f).app N := by
  let P := projectiveResolution N
  have hm := derivedTensorModuleModelIso_naturality f (𝟙 N)
  simp only [CategoryTheory.Functor.map_id] at hm
  have hLift : Homotopy (extLift P (𝟙 N) P) (𝟙 (extRes P)) := by
    simpa only [extLift, HomologicalComplex.extendMap_id] using
      (ProjectiveResolution.liftIdHomotopy N P).extend embUp
  have ht := cochainTensorHomotopyRight
    ((CochainComplex.singleFunctor (ModuleCat R) 0).map f) hLift
  rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R) ht] at hm
  have hr := realizedDerivedTensorResolutionIso_naturality_left f P
  apply (cancel_mono (realizedDerivedTensorResolutionIso M' P).hom).mp
  dsimp only [boundedAboveDerivedTensorModuleFunctor, P] at *
  simp only [boundedAboveDerivedTensorModuleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hm, Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    cochainTensorSingleLeftIso_module_naturality, CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map
    (mapExtendIso_natTrans (tensorLeft M) P.complex embUp ((tensoringLeft (ModuleCat R)).map f))

/-- The comparison is a natural isomorphism in the right argument. -/
def boundedAboveDerivedTensorModuleNatIso (M : ModuleCat.{u} R) :
    boundedAboveDerivedTensorModuleFunctor M ≅ realizedDerivedTensorFunctor R M :=
  NatIso.ofComponents (boundedAboveDerivedTensorModuleIso M)
    (fun g => boundedAboveDerivedTensorModuleIso_naturality_right M g)

/-- In degree zero the actual tensor recovers the ordinary tensor product naturally. -/
def boundedAboveDerivedTensorModuleH0NatIso (M : ModuleCat.{u} R) :
    boundedAboveDerivedTensorModuleFunctor M ⋙ DerivedCategory.homologyFunctor (ModuleCat R) 0 ≅
      tensorLeft M :=
  Functor.isoWhiskerRight (boundedAboveDerivedTensorModuleNatIso M) _ ≪≫
    realizedDerivedTensorH0NatIso R M

/-- In every negative degree the actual tensor recovers the existing Tor functor naturally. -/
def boundedAboveDerivedTensorModuleTorNatIso (M : ModuleCat.{u} R) (n : ℕ) :
    boundedAboveDerivedTensorModuleFunctor M ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) (-(n : ℤ)) ≅
      (Tor (ModuleCat.{u} R) n).obj M :=
  Functor.isoWhiskerRight (boundedAboveDerivedTensorModuleNatIso M) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chainDerivedRealizationHomologyIso R n)

/-- Transport the existing standard augmentation through the proved comparison. -/
def boundedAboveDerivedTensorModuleAugmentation (M : ModuleCat.{u} R) :
    boundedAboveDerivedTensorModuleFunctor M ⟶
      tensorLeft M ⋙ DerivedCategory.singleFunctor (ModuleCat R) 0 :=
  (boundedAboveDerivedTensorModuleNatIso M).hom ≫ realizedDerivedTensorAugmentation R M

/-- The transported augmentation induces the standard ordinary tensor comparison on H0. -/
lemma boundedAboveDerivedTensorModuleAugmentation_homology (M N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedTensorModuleAugmentation M).app N) ≫
      (realizedSingleH0Iso R).hom.app ((tensorLeft M).obj N) =
        (boundedAboveDerivedTensorModuleH0NatIso M).hom.app N := by
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    ((boundedAboveDerivedTensorModuleNatIso M).hom.app N ≫
      (realizedDerivedTensorAugmentation R M).app N) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, realizedDerivedTensorAugmentation_homology]
  rfl

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.0.0.1" (partial := component) "仮定：通常可換環 R 上の離散な二加群と有界上の通常導来テンソル（Lean が強い：通常の dg 導来模型の場合）。結論：導来テンソルの H⁻ⁿ を通常の Torₙ と自然同型にする（原典が 7.2.1.22 を引用する Tor 計算の部分に一致）。HR 加群スペクトルとの比較および一般の非可換環は含まれない。"] _root_.SerrePositivity.boundedAboveDerivedTensorModuleTorNatIso
attribute [cite HA "7.2.1.22" (partial := special) "仮定：通常の可換環 R の離散な二つの加群（Lean が強い：可換環の通常の導来圏模型）。結論：その導来テンソルの H⁻ⁿ を Torₙ と自然に同定する（離散入力での HA の結論に一致する部分）。環スペクトルのテンソルとの比較は含まれない。"] _root_.SerrePositivity.boundedAboveDerivedTensorModuleTorNatIso
attribute [cite HA "7.2.1.23" (partial := component) "仮定：通常の可換環 R の離散な二つの加群（Lean が強い：基底と入力がすべて離散な通常の導来圏模型）。結論：導来テンソルの H⁰ を通常テンソルに自然に同定する（結論 (2) のこの場合に一致）。一般の連結入力の連結性と環スペクトルへの比較は含まれない。"] _root_.SerrePositivity.boundedAboveDerivedTensorModuleH0NatIso
