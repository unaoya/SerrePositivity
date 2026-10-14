module

public import SerrePositivity.HomologicalAlgebra.KoszulTorComparison
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl
public import SerrePositivity.HomologicalAlgebra.LinearFunctorScalarCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower

/-! # 係数付きKoszul複体のテンソルモデルと反復錐モデル

比較は任意の係数加群とその写像に自然であり、有限性や平坦性を要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- 係数付きKoszulの二つのモデルの標準比較。 -/
def koszulTensorConeIso : ∀ {n : ℕ} (z : Fin n → R) (M : ModuleCat.{u} R),
    (koszulTensorModuleFunctor z).obj M ≅ (koszulModuleFunctor z).obj M
  | 0, _, M =>
      (singleMapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).obj M)
        (c := ComplexShape.up ℤ) 0).app (ModuleCat.of R R) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso (ρ_ M)
  | n + 1, z, M =>
      linearFunctorScalarConeIso ((tensoringLeft (ModuleCat.{u} R)).obj M)
        (z (Fin.last n)) (koszulComplex (Fin.init z)) ≪≫
      (scalarConeFunctor (z (Fin.last n))).mapIso (koszulTensorConeIso (Fin.init z) M)

/-- 標準比較は、係数加群の任意の射に自然。 -/
@[reassoc] theorem koszulTensorConeIso_naturality {n : ℕ} (z : Fin n → R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (koszulTensorModuleFunctor z).map f ≫ (koszulTensorConeIso z N).hom =
      (koszulTensorConeIso z M).hom ≫ (koszulModuleFunctor z).map f := by
  induction n with
  | zero =>
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    change f ▷ (𝟙_ (ModuleCat.{u} R)) ≫ 𝟙 (N ⊗ (𝟙_ _)) ≫ (ρ_ N).hom ≫ 𝟙 N =
      𝟙 (M ⊗ (𝟙_ _)) ≫ (ρ_ M).hom ≫ 𝟙 M ≫ f ≫ 𝟙 N
    simp
  | succ n ih =>
    change (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f) _).app
      ((scalarConeFunctor (z (Fin.last n))).obj (koszulComplex (Fin.init z))) ≫
      ((linearFunctorScalarConeIso ((tensoringLeft (ModuleCat.{u} R)).obj N)
        (z (Fin.last n)) (koszulComplex (Fin.init z))).hom ≫
        (scalarConeFunctor (z (Fin.last n))).map (koszulTensorConeIso (Fin.init z) N).hom) =
      ((linearFunctorScalarConeIso ((tensoringLeft (ModuleCat.{u} R)).obj M)
        (z (Fin.last n)) (koszulComplex (Fin.init z))).hom ≫
        (scalarConeFunctor (z (Fin.last n))).map (koszulTensorConeIso (Fin.init z) M).hom) ≫
        (scalarConeFunctor (z (Fin.last n))).map ((koszulModuleFunctor (Fin.init z)).map f)
    rw [← Category.assoc, linearFunctorScalarConeIso_natTrans, Category.assoc,
      ← Functor.map_comp]
    erw [ih (Fin.init z)]
    rw [Functor.map_comp, Category.assoc]

/-- 複体の比較を自然同型として公開する。 -/
def koszulTensorConeNatIso {n : ℕ} (z : Fin n → R) :
    koszulTensorModuleFunctor z ≅ koszulModuleFunctor z :=
  NatIso.ofComponents (koszulTensorConeIso z) (fun f ↦ koszulTensorConeIso_naturality z f)

/-- 既存の反復錐モデルのKoszulホモロジーとTorの自然同型。 -/
def koszulModuleTorComparison {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip.obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≅
      koszulModuleFunctor z ⋙ HomologicalComplex.homologyFunctor _ _ (-(i : ℤ)) :=
  koszulTorComparison z hz i ≪≫ Functor.isoWhiskerRight (koszulTensorConeNatIso z) _

/-- 基底環上のKoszul複体の射は、テンソル係数モデルの自然変換を誘導する。 -/
def koszulTensorCoefficientMapOfComplexMap {m n : ℕ} (z : Fin m → R) (w : Fin n → R)
    (φ : koszulComplex z ⟶ koszulComplex w) :
    koszulTensorModuleFunctor z ⟶ koszulTensorModuleFunctor w where
  app M := (((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex _).map φ
  naturality _ _ f :=
    ((NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f) _).naturality φ).symm

/-- 反復錐モデルにおける、基底環のKoszul写像からの係数付き写像。 -/
def koszulModuleCoefficientMapOfComplexMap {m n : ℕ} (z : Fin m → R) (w : Fin n → R)
    (φ : koszulComplex z ⟶ koszulComplex w) :
    koszulModuleFunctor z ⟶ koszulModuleFunctor w :=
  (koszulTensorConeNatIso z).inv ≫ koszulTensorCoefficientMapOfComplexMap z w φ ≫
    (koszulTensorConeNatIso w).hom

/-- 任意のKoszul写像について、二モデルの比較は可換。冪の遷移にも適用できる。 -/
theorem koszulTensorConeNatIso_complex_map_compatibility {m n : ℕ}
    (z : Fin m → R) (w : Fin n → R) (φ : koszulComplex z ⟶ koszulComplex w) :
    koszulTensorCoefficientMapOfComplexMap z w φ ≫ (koszulTensorConeNatIso w).hom =
    (koszulTensorConeNatIso z).hom ≫ koszulModuleCoefficientMapOfComplexMap z w φ := by
  simp [koszulModuleCoefficientMapOfComplexMap, ← Category.assoc]

@[simp] theorem koszulModuleCoefficientMapOfComplexMap_id {n : ℕ} (z : Fin n → R) :
    koszulModuleCoefficientMapOfComplexMap z z (𝟙 _) = 𝟙 (koszulModuleFunctor z) := by
  have h : koszulTensorCoefficientMapOfComplexMap z z (𝟙 _) = 𝟙 (koszulTensorModuleFunctor z) := by
    apply NatTrans.ext
    funext M
    exact CategoryTheory.Functor.map_id
      (((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex (.up ℤ)) (koszulComplex z)
  simp only [koszulModuleCoefficientMapOfComplexMap, h, Category.id_comp, Iso.inv_hom_id]

@[simp] theorem koszulModuleCoefficientMapOfComplexMap_comp {l m n : ℕ}
    (x : Fin l → R) (z : Fin m → R) (w : Fin n → R)
    (φ : koszulComplex x ⟶ koszulComplex z) (ψ : koszulComplex z ⟶ koszulComplex w) :
    koszulModuleCoefficientMapOfComplexMap x w (φ ≫ ψ) =
      koszulModuleCoefficientMapOfComplexMap x z φ ≫
        koszulModuleCoefficientMapOfComplexMap z w ψ := by
  apply NatTrans.ext
  funext M
  simp [koszulModuleCoefficientMapOfComplexMap,
    koszulTensorCoefficientMapOfComplexMap, Category.assoc]

/-- 既存の冪のKoszul遷移を、任意の係数加群の反復錐モデルへ移す。 -/
def powerKoszulModuleTransition {n : ℕ} (z : Fin n → R) (q : ℕ) :
    koszulModuleFunctor (fun j ↦ z j ^ (q + 1)) ⟶ koszulModuleFunctor (fun j ↦ z j ^ q) :=
  koszulModuleCoefficientMapOfComplexMap _ _ (DerivedCompletion.powerKoszulTransition R z q)

/-- 冪の塔の遷移と二モデルの比較の可換図式。 -/
theorem koszulTensorConeNatIso_power_transition {n : ℕ} (z : Fin n → R) (q : ℕ) :
    koszulTensorCoefficientMapOfComplexMap _ _ (DerivedCompletion.powerKoszulTransition R z q) ≫
      (koszulTensorConeNatIso (fun j ↦ z j ^ q)).hom =
    (koszulTensorConeNatIso (fun j ↦ z j ^ (q + 1))).hom ≫ powerKoszulModuleTransition z q :=
  koszulTensorConeNatIso_complex_map_compatibility _ _ _

/-- Torと反復錐のホモロジー比較の、任意の係数写像に関する図式。 -/
@[reassoc] theorem koszulModuleTorComparison_naturality {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) i).map f).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≫
      ((koszulModuleTorComparison z hz i).app N).hom =
    ((koszulModuleTorComparison z hz i).app M).hom ≫
      (koszulModuleFunctor z ⋙ HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).map f :=
  (koszulModuleTorComparison z hz i).hom.naturality f

/-- 反復錐のホモロジーでも、係数写像の零性とTor上の零性は同値。 -/
theorem koszulModuleTorComparison_map_eq_zero_iff {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) i).map f).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) = 0 ↔
      (koszulModuleFunctor z ⋙ HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).map f = 0 := by
  constructor
  · intro hf
    rw [← cancel_epi ((koszulModuleTorComparison z hz i).app M).hom, comp_zero,
      ← koszulModuleTorComparison_naturality, hf, zero_comp]
  · intro hf
    rw [← cancel_mono ((koszulModuleTorComparison z hz i).app N).hom, zero_comp,
      koszulModuleTorComparison_naturality, hf, comp_zero]

/-- 全試験加群でのTor零作用を、既存のKoszulホモロジー上の具体的自己射の零性へ移す。 -/
theorem koszulModuleHomology_coefficient_scalar_eq_zero_of_tor_annihilated
    {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z)
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (i : ℕ), 0 < i →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N i c = 0)
    (i : ℕ) (hi : 0 < i) (c : C) (hc : c ∈ I) :
    HomologicalComplex.homologyMap
      ((koszulModuleFunctor z).map (ModuleCat.ofHom (LinearMap.mulLeft R c))) (-(i : ℤ)) = 0 :=
  (koszulModuleTorComparison_map_eq_zero_iff z hz i
    (ModuleCat.ofHom (LinearMap.mulLeft R c))).mp (hTor _ i hi c hc)

/-- 正則パラメータの正の冪についても、反復錐モデルへの比較は任意の係数加群に自然。 -/
def koszulModuleTorPowersComparison [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z))
    (v : ℕ) (hv : 0 < v) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip.obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun j ↦ z j ^ v)))) ≅
      koszulModuleFunctor (fun j ↦ z j ^ v) ⋙
        HomologicalComplex.homologyFunctor _ _ (-(i : ℤ)) :=
  koszulModuleTorComparison _ (isKoszulResolution_powers_of_isWeaklyRegular z hz hreg v hv) i

end SerrePositivity
