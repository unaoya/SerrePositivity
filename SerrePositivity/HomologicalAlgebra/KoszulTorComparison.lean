module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.ResolutionNaturality
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.CommutativeAlgebra.Koszul.Powers

/-! # 任意の係数加群に自然なKoszul–Tor比較

既存のKoszul複体に通常テンソル関手を施した係数付き複体を使う。
Koszul複体が商の射影分解なら、そのホモロジーとTorは係数加群に自然に同型。
係数加群の有限性、平坦性、導来完備性は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- 標準Koszul複体と係数加群のテンソル。射にも同じテンソルを適用する。 -/
def koszulTensorModuleFunctor {n : ℕ} (z : Fin n → R) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := (((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex _).obj (koszulComplex z)
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map f) _).app
    (koszulComplex z)
  map_id M := by
    ext i
    simp
  map_comp f g := by
    ext i
    simp

/-- 係数付きKoszulホモロジーを、任意加群の関手として扱う。 -/
abbrev koszulTensorModuleHomologyFunctor {n : ℕ} (z : Fin n → R) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  koszulTensorModuleFunctor z ⋙ HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))

/-- Koszul分解によるTorの計算は、全ての係数加群に自然。 -/
def koszulTorComparison {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip.obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≅
      koszulTensorModuleHomologyFunctor z i :=
  NatIso.ofComponents (fun M ↦ torModuleIsoCochain M (isResolutionOf_koszul z hz) i)
    (fun f ↦ leftDerivedIsoCochain_natTrans _ _ ((tensoringLeft (ModuleCat.{u} R)).map f)
      (isResolutionOf_koszul z hz) i)

/-- 比較は、長さだけでなく実際のホモロジー加群の同型を与える。 -/
def koszulTorComparisonEquiv {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z)
    (i : ℕ) (M : ModuleCat.{u} R) :
    ((koszulTensorModuleFunctor z).obj M).homology (-(i : ℤ)) ≃ₗ[R]
      ((Tor (ModuleCat.{u} R) i).obj M).obj (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) :=
  ((koszulTorComparison z hz i).app M).symm.toLinearEquiv

/-- 任意の係数写像についての、比較の可換図式。 -/
@[reassoc] theorem koszulTorComparison_naturality {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) i).map f).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≫
      ((koszulTorComparison z hz i).app N).hom =
    ((koszulTorComparison z hz i).app M).hom ≫
      (koszulTensorModuleHomologyFunctor z i).map f :=
  (koszulTorComparison z hz i).hom.naturality f

/-- 比較を通じて係数写像の零性を保存・反映する。 -/
theorem koszulTorComparison_map_eq_zero_iff {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) i).map f).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) = 0 ↔
      (koszulTensorModuleHomologyFunctor z i).map f = 0 := by
  constructor
  · intro hf
    rw [← cancel_epi ((koszulTorComparison z hz i).app M).hom, comp_zero,
      ← koszulTorComparison_naturality, hf, zero_comp]
  · intro hf
    rw [← cancel_mono ((koszulTorComparison z hz i).app N).hom, zero_comp,
      koszulTorComparison_naturality, hf, comp_zero]

/-- 係数代数の元が、Torの第1変数の乗法写像として誘導する自己射。 -/
def torCoefficientScalarEndomorphism (C : Type u) [CommRing C] [Algebra R C]
    (N : ModuleCat.{u} R) (i : ℕ) (c : C) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj N ⟶
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj N :=
  ((Tor (ModuleCat.{u} R) i).map (ModuleCat.ofHom (LinearMap.mulLeft R c))).app N

/-- 同じ乗法写像が、係数付きKoszulホモロジーに誘導する自己射。 -/
def koszulTensorCoefficientScalarEndomorphism {n : ℕ} (z : Fin n → R)
    (C : Type u) [CommRing C] [Algebra R C] (i : ℕ) (c : C) :
    (koszulTensorModuleHomologyFunctor z i).obj (ModuleCat.of R C) ⟶
      (koszulTensorModuleHomologyFunctor z i).obj (ModuleCat.of R C) :=
  (koszulTensorModuleHomologyFunctor z i).map (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- 任意の係数元の作用とTor比較は可換である。 -/
@[reassoc] theorem koszulTorComparison_coefficient_scalar {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (C : Type u) [CommRing C] [Algebra R C] (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) i c ≫
      ((koszulTorComparison z hz i).app (ModuleCat.of R C)).hom =
    ((koszulTorComparison z hz i).app (ModuleCat.of R C)).hom ≫
      koszulTensorCoefficientScalarEndomorphism z C i c :=
  koszulTorComparison_naturality z hz i (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- 係数元のTor上の零作用を、Koszulホモロジー上の零作用へ移す。 -/
theorem koszulTensorCoefficientScalar_eq_zero_iff {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (C : Type u) [CommRing C] [Algebra R C] (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) i c = 0 ↔
      koszulTensorCoefficientScalarEndomorphism z C i c = 0 :=
  koszulTorComparison_map_eq_zero_iff z hz i (ModuleCat.ofHom (LinearMap.mulLeft R c))

/-- 全ての試験加群に対する高次TorのI零化は、正則Koszulホモロジーを零化する。
試験加群の導来完備性や有限性を追加しない。 -/
theorem koszulTensorCoefficientScalar_eq_zero_of_tor_annihilated
    {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z)
    (C : Type u) [CommRing C] [Algebra R C] (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (i : ℕ), 0 < i →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N i c = 0)
    (i : ℕ) (hi : 0 < i) (c : C) (hc : c ∈ I) :
    koszulTensorCoefficientScalarEndomorphism z C i c = 0 :=
  (koszulTensorCoefficientScalar_eq_zero_iff z hz C i c).mp (hTor _ i hi c hc)

/-- 正則パラメータ列の正の冪についての、係数加群に自然な比較。 -/
def koszulTorPowersComparison [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn z))
    (v : ℕ) (hv : 0 < v) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).flip.obj
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun j ↦ z j ^ v)))) ≅
      koszulTensorModuleHomologyFunctor (fun j ↦ z j ^ v) i :=
  koszulTorComparison _ (isKoszulResolution_powers_of_isWeaklyRegular z hz hreg v hv) i

end SerrePositivity
