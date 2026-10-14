module

public import SerrePositivity.HomologicalAlgebra.DerivedTensor
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # 導来テンソルの実導来圏への実現

既存の非負鎖複体のホモトピー類を、`n ↦ -n` の延長と実局所化で
標準の導来圏へ移す。延長のホモロジー比較は自然同型として構成する。
-/

@[expose] public noncomputable section

universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SerrePositivity

attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 非負鎖複体のホモトピー類を標準の実導来圏へ移す関手。 -/
def chainDerivedRealization :
    HomotopyCategory (ModuleCat.{u} R) (.down ℕ) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  embUp.extendHomotopyFunctor (ModuleCat.{u} R) ⋙ DerivedCategory.Qh

/-- 延長は鎖次数nのホモロジーを余鎖次数-nへ移す。 -/
def extendChainHomologyIso (n : ℕ) :
    embUp.extendFunctor (ModuleCat.{u} R) ⋙
      HomologicalComplex.homologyFunctor _ (.up ℤ) (-(n : ℤ)) ≅
    HomologicalComplex.homologyFunctor _ (.down ℕ) n :=
  NatIso.ofComponents (fun K ↦ K.extendHomologyIso embUp (by simp [embUp]))
    (fun f ↦ HomologicalComplex.extendHomologyIso_hom_naturality f embUp
      (by simp [embUp]))

/-- 延長のホモロジー比較をホモトピー圏に降ろした自然同型。 -/
def extendHomotopyChainHomologyIso (n : ℕ) :
    embUp.extendHomotopyFunctor (ModuleCat.{u} R) ⋙
      HomotopyCategory.homologyFunctor _ (.up ℤ) (-(n : ℤ)) ≅
    HomotopyCategory.homologyFunctor _ (.down ℕ) n :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (embUp.extendHomotopyFunctorFactors (ModuleCat.{u} R)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (embUp.extendFunctor (ModuleCat.{u} R))
        (HomotopyCategory.homologyFunctorFactors _ _ _) ≪≫
      extendChainHomologyIso R n ≪≫
      (HomotopyCategory.homologyFunctorFactors _ _ _).symm)

/-- 実局所化も含めた、全ホモトピー類に自然な次数比較。 -/
def chainDerivedRealizationHomologyIso (n : ℕ) :
    chainDerivedRealization R ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ)) ≅
    HomotopyCategory.homologyFunctor _ (.down ℕ) n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (embUp.extendHomotopyFunctor (ModuleCat.{u} R))
      (DerivedCategory.homologyFunctorFactorsh _ _) ≪≫
    extendHomotopyChainHomologyIso R n

/-- 非負鎖複体から零次ホモロジーを零次数に置いた複体への標準射。 -/
def chainHomologyZeroProjection (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    K ⟶ (HomologicalComplex.single _ (.down ℕ) 0).obj (K.homology 0) :=
  HomologicalComplex.mkHomToSingle
    (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) (by simp)

/-- 標準射は複体の射に自然。 -/
@[reassoc] theorem chainHomologyZeroProjection_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) :
    f ≫ chainHomologyZeroProjection R L = chainHomologyZeroProjection R K ≫
      (HomologicalComplex.single _ (.down ℕ) 0).map (HomologicalComplex.homologyMap f 0) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, chainHomologyZeroProjection,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.p_opcyclesMap_assoc, ← ChainComplex.isoHomologyι₀_inv_naturality_assoc]

/-- 標準射がH₀に誘導する射は標準の単一複体比較の逆射。 -/
theorem chainHomologyZeroProjection_homology (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.homologyMap (chainHomologyZeroProjection R K) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (K.homology 0)).hom = 𝟙 _ := by
  rw [← HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv,
    HomologicalComplex.homologyι_naturality_assoc]
  apply (cancel_epi K.isoHomologyι₀.inv).mp
  change K.isoHomologyι₀.inv ≫ K.isoHomologyι₀.hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc, Category.comp_id, ← cancel_epi (K.pOpcycles 0)]
  simp only [HomologicalComplex.p_opcyclesMap_assoc, chainHomologyZeroProjection,
    HomologicalComplex.mkHomToSingle_f, Category.assoc]
  rw [HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv]
  simp

/-- 零次ホモロジーへの標準射を自然変換としてまとめる。 -/
def chainHomologyZeroProjectionNatTrans :
    𝟭 (ChainComplex (ModuleCat.{u} R) ℕ) ⟶
      HomologicalComplex.homologyFunctor _ (.down ℕ) 0 ⋙
        HomologicalComplex.single _ (.down ℕ) 0 where
  app := chainHomologyZeroProjection R
  naturality _ _ f := chainHomologyZeroProjection_naturality R f

/-- 標準射をホモトピー圏へ降ろす。 -/
def homotopyChainHomologyZeroProjection :
    𝟭 (HomotopyCategory (ModuleCat.{u} R) (.down ℕ)) ⟶
      HomotopyCategory.homologyFunctor _ (.down ℕ) 0 ⋙
        HomologicalComplex.single _ (.down ℕ) 0 ⋙ HomotopyCategory.quotient _ _ := by
  refine CategoryTheory.Quotient.natTransLift _ ?_
  exact (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (chainHomologyZeroProjectionNatTrans R) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerRight (HomotopyCategory.homologyFunctorFactors _ _ _).inv _ ≫
    (Functor.associator _ _ _).hom

/-- ホモトピー圏における単一鎖複体のH₀比較。 -/
def homotopyChainSingleHomologyIso :
    (HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0 ⋙
      HomotopyCategory.quotient _ _) ⋙ HomotopyCategory.homologyFunctor _ _ 0 ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (HomotopyCategory.homologyFunctorFactors _ _ _) ≪≫
    HomologicalComplex.homologyFunctorSingleIso _ _ _

/-- ホモトピー圏上の射もH₀上で恒等射を誘導する。 -/
theorem homotopyChainHomologyZeroProjection_homology
    (K : HomotopyCategory (ModuleCat.{u} R) (.down ℕ)) :
    (HomotopyCategory.homologyFunctor _ _ 0).map
        ((homotopyChainHomologyZeroProjection R).app K) ≫
      (homotopyChainSingleHomologyIso R).hom.app
        ((HomotopyCategory.homologyFunctor _ _ 0).obj K) = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let e := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).app K
  change (HomotopyCategory.homologyFunctor _ _ 0).map
    ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K) ≫
      (HomologicalComplex.single _ (.down ℕ) 0 ⋙ HomotopyCategory.quotient _ _).map e.inv) ≫ _ = _
  have hn := (homotopyChainSingleHomologyIso R).hom.naturality e.inv
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Category.assoc]
  erw [hn]
  change (HomotopyCategory.homologyFunctor _ _ 0).map
    ((HomotopyCategory.quotient _ _).map (chainHomologyZeroProjection R K)) ≫
    (HomotopyCategory.homologyFunctorFactors _ _ 0).hom.app _ ≫
    (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (K.homology 0)).hom ≫
    e.inv = 𝟙 _
  have hf := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.down ℕ) 0).hom.naturality
    (chainHomologyZeroProjection R K)
  simp only [Functor.comp_map] at hf
  erw [← Category.assoc, ← Category.assoc, hf]
  change e.hom ≫ HomologicalComplex.homologyMap (chainHomologyZeroProjection R K) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0 (K.homology 0)).hom ≫ e.inv = _
  rw [← Category.assoc (HomologicalComplex.homologyMap _ _) _,
    chainHomologyZeroProjection_homology, Category.id_comp]
  exact e.hom_inv_id

/-- 実現の複体上での計算を与える自然同型。 -/
def chainDerivedRealizationComplexNatIso :
    HomotopyCategory.quotient (ModuleCat.{u} R) (.down ℕ) ⋙ chainDerivedRealization R ≅
      embUp.extendFunctor (ModuleCat.{u} R) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (embUp.extendHomotopyFunctorFactors (ModuleCat.{u} R)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)

/-- 零次数の単一複体の延長比較。 -/
def extendChainSingleNatIso :
    HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0 ⋙
      embUp.extendFunctor _ ≅ HomologicalComplex.single _ (.up ℤ) 0 :=
  NatIso.ofComponents
    (fun X ↦ HomologicalComplex.extendSingleIso embUp X 0 0 (by simp [embUp]))
    (fun f ↦ by
      apply HomologicalComplex.to_single_hom_ext
      simp [HomologicalComplex.extendSingleIso_hom_f,
        HomologicalComplex.extendMap_f _ embUp (show embUp.f 0 = 0 by simp [embUp]),
        HomologicalComplex.single_map_f_self])

/-- 単一複体の実現は標準の零次数導来対象である。 -/
def chainDerivedRealizationSingleNatIso :
    (HomologicalComplex.single (ModuleCat.{u} R) (.down ℕ) 0 ⋙
      HomotopyCategory.quotient _ _) ⋙ chainDerivedRealization R ≅
      DerivedCategory.singleFunctor _ 0 :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chainDerivedRealizationComplexNatIso R) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendChainSingleNatIso R) _

/-- 任意の非負鎖ホモトピー類からH₀の零次数導来対象への標準augmentation。 -/
def chainDerivedAugmentation : chainDerivedRealization R ⟶
    HomotopyCategory.homologyFunctor _ (.down ℕ) 0 ⋙
      DerivedCategory.singleFunctor _ 0 :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (homotopyChainHomologyZeroProjection R) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (chainDerivedRealizationSingleNatIso R).hom

/-- 標準射の実現とH⁰比較の可換図式。 -/
theorem chainDerivedAugmentation_homology_diagram
    (K : HomotopyCategory (ModuleCat.{u} R) (.down ℕ)) :
    (DerivedCategory.homologyFunctor _ 0).map
        ((chainDerivedRealization R).map ((homotopyChainHomologyZeroProjection R).app K)) ≫
      (chainDerivedRealizationHomologyIso R 0).hom.app _ ≫
      (homotopyChainSingleHomologyIso R).hom.app
        ((HomotopyCategory.homologyFunctor _ (.down ℕ) 0).obj K) =
      (chainDerivedRealizationHomologyIso R 0).hom.app K := by
  have hn := (chainDerivedRealizationHomologyIso R 0).hom.naturality
    ((homotopyChainHomologyZeroProjection R).app K)
  simp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn]
  rw [Category.assoc, homotopyChainHomologyZeroProjection_homology, Category.comp_id]
  rfl

/-- 単一導来対象のH⁰比較を、鎖複体の標準比較から構成する。 -/
def realizedSingleH0Iso :
    DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
      DerivedCategory.homologyFunctor _ 0 ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (chainDerivedRealizationSingleNatIso R).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chainDerivedRealizationHomologyIso R 0) ≪≫
    homotopyChainSingleHomologyIso R

/-- 実導来圏におけるaugmentationのH⁰図式。 -/
theorem chainDerivedAugmentation_homology
    (K : HomotopyCategory (ModuleCat.{u} R) (.down ℕ)) :
    (DerivedCategory.homologyFunctor _ 0).map ((chainDerivedAugmentation R).app K) ≫
      (realizedSingleH0Iso R).hom.app
        ((HomotopyCategory.homologyFunctor _ (.down ℕ) 0).obj K) =
      (chainDerivedRealizationHomologyIso R 0).hom.app K := by
  dsimp [chainDerivedAugmentation, realizedSingleH0Iso]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map_comp_assoc
    ((chainDerivedRealizationSingleNatIso R).hom.app _)
    ((chainDerivedRealizationSingleNatIso R).inv.app _),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact chainDerivedAugmentation_homology_diagram R K

/-- 非負鎖複体の実現は正の余鎖次数にホモロジーを持たない。 -/
theorem chainDerivedRealization_homology_isZero_positive
    (K : HomotopyCategory (ModuleCat.{u} R) (.down ℕ)) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj ((chainDerivedRealization R).obj K)) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
    ((chainDerivedRealizationComplexNatIso R).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _
  apply e.isZero_iff.mpr
  apply (HomologicalComplex.extend_exactAt K embUp i ?_).isZero_homology
  intro n hn
  have hnonpos : embUp.f n ≤ 0 := by simp [embUp]
  omega

/-- 第2変数に関する実導来テンソル関手。 -/
def realizedDerivedTensorFunctor (M : ModuleCat.{u} R) :
    ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedToHomotopyCategory ⋙
    chainDerivedRealization R

/-- 第1変数の写像も自然変換として実現する。 -/
def realizedDerivedTensorMapLeft {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    realizedDerivedTensorFunctor R M ⟶ realizedDerivedTensorFunctor R M' :=
  Functor.whiskerRight
    (NatTrans.leftDerivedToHomotopyCategory ((tensoringLeft (ModuleCat.{u} R)).map f)) _

@[simp] theorem realizedDerivedTensorMapLeft_id (M : ModuleCat.{u} R) :
    realizedDerivedTensorMapLeft R (𝟙 M) = 𝟙 (realizedDerivedTensorFunctor R M) := by
  simp [realizedDerivedTensorMapLeft]
  rfl

@[simp] theorem realizedDerivedTensorMapLeft_comp {M M' M'' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    realizedDerivedTensorMapLeft R (f ≫ g) =
      realizedDerivedTensorMapLeft R f ≫ realizedDerivedTensorMapLeft R g := by
  simp [realizedDerivedTensorMapLeft]

/-- H⁰と通常テンソルの比較は第2変数に自然。 -/
def realizedDerivedTensorH0NatIso (M : ModuleCat.{u} R) :
    realizedDerivedTensorFunctor R M ⋙ DerivedCategory.homologyFunctor _ 0 ≅
      (tensoringLeft (ModuleCat.{u} R)).obj M :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (chainDerivedRealizationHomologyIso R 0) ≪≫
    ((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf

/-- 通常テンソルの零次数導来対象への標準augmentation。 -/
def realizedDerivedTensorAugmentation (M : ModuleCat.{u} R) :
    realizedDerivedTensorFunctor R M ⟶
      (tensoringLeft (ModuleCat.{u} R)).obj M ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.whiskerLeft _ (chainDerivedAugmentation R) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.hom _

/-- 既存の導来テンソルを標準の実導来圏へ実現した対象。 -/
abbrev realizedDerivedTensor (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : DerivedCategory (ModuleCat.{u} R) :=
  (chainDerivedRealization R).obj (derivedTensor R M N)

/-- 実現された導来テンソルのH^{-n}は既存のTor_nと同型。 -/
def realizedDerivedTensorHomologyIso (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).obj
      (realizedDerivedTensor R M N) ≅
    ((Tor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).obj (ModuleCat.of R N) :=
  (chainDerivedRealizationHomologyIso R n).app (derivedTensor R M N)

/-- H⁰は通常のテンソル積である。高次Tor消滅は仮定しない。 -/
def realizedDerivedTensorH0Iso (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      (realizedDerivedTensor R M N) ≅ ModuleCat.of R (TensorProduct R M N) :=
  realizedDerivedTensorHomologyIso R M N 0 ≪≫
    (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf).app
      (ModuleCat.of R N)

/-- 実導来augmentationのH⁰は通常テンソルとの標準比較である。 -/
theorem realizedDerivedTensorAugmentation_homology (M N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor _ 0).map
        ((realizedDerivedTensorAugmentation R M).app N) ≫
      (realizedSingleH0Iso R).hom.app
        (((tensoringLeft (ModuleCat.{u} R)).obj M).obj N) =
      (realizedDerivedTensorH0NatIso R M).hom.app N := by
  have hn := (realizedSingleH0Iso R).hom.naturality
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.hom.app N)
  simp only [Functor.comp_map, Functor.id_map] at hn
  change (DerivedCategory.homologyFunctor _ 0).map
    ((chainDerivedAugmentation R).app _ ≫ (DerivedCategory.singleFunctor _ 0).map
      (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.hom.app N)) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  erw [chainDerivedAugmentation_homology]
  rfl

/-- 離散性は実現により保存・反映される。高次Tor消滅を隠れた仮定にしない。 -/
theorem realizedDerivedTensor_discrete_iff (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (realizedDerivedTensor R M N))) ↔ IsConcentratedInDegreeZero (derivedTensor R M N) := by
  constructor
  · intro h n hn
    exact (chainDerivedRealizationHomologyIso R n).app (derivedTensor R M N) |>.isZero_iff.mp
      (h (-(n : ℤ)) (by omega))
  · intro h i hi
    by_cases hpos : 0 < i
    · exact chainDerivedRealization_homology_isZero_positive R _ i hpos
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = -(n : ℤ) := by
        exact ⟨(-i).toNat, by omega⟩
      subst i
      exact ((chainDerivedRealizationHomologyIso R n).app (derivedTensor R M N)).isZero_iff.mpr
        (h n (by omega))

end SerrePositivity
