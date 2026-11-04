module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
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

/-- 任意の係数写像についての、比較の可換図式。 -/
@[reassoc] theorem koszulTorComparison_naturality {n : ℕ} (z : Fin n → R)
    (hz : IsKoszulResolution z) (i : ℕ) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((Tor (ModuleCat.{u} R) i).map f).app (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≫
      ((koszulTorComparison z hz i).app N).hom =
    ((koszulTorComparison z hz i).app M).hom ≫
      (koszulTensorModuleHomologyFunctor z i).map f :=
  (koszulTorComparison z hz i).hom.naturality f

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

end SerrePositivity
