module

public import SerrePositivity.HomologicalAlgebra.KoszulTensorConeComparison

/-! # 代数上の通常のKoszulホモロジーとTorの係数作用

比較は底環上の加群同型として構成するが、代数の元による標準作用とも両立する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]

/-- 係数拡大後に制限した複体を、Cとの通常テンソルとして比較する。 -/
def algebraBaseChangeTensorIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).obj
      (baseChange (algebraMap R C) K) ≅
      (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R C)).mapHomologicalComplex _).obj K :=
  (Functor.mapHomologicalComplexCompIso (extendRestrictScalarsTensorIso (R := R) (T := C)) _).app K

/-- 上の比較はCの元による乗法とも両立する。 -/
@[reassoc] theorem algebraBaseChangeTensorIso_coefficient_scalar
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : C) :
    ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).map
        (c • 𝟙 (baseChange (algebraMap R C) K)) ≫
      (algebraBaseChangeTensorIso (C := C) K).hom =
    (algebraBaseChangeTensorIso (C := C) K).hom ≫
      (NatTrans.mapHomologicalComplex
        ((tensoringLeft (ModuleCat.{u} R)).map
          (ModuleCat.ofHom (LinearMap.mulLeft R c))) _).app K := by
  ext i x
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp_all only [map_add]

/-- 係数テンソルモデルと、代数C上の通常のKoszul複体の係数制限の比較。 -/
def algebraKoszulTensorIso {n : ℕ} (z : Fin n → R) :
    (koszulTensorModuleFunctor z).obj (ModuleCat.of R C) ≅
      ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).obj
        (koszulComplex (algebraMap R C ∘ z)) :=
  (algebraBaseChangeTensorIso (C := C) (koszulComplex z)).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).mapIso
      (baseChangeKoszulIso (algebraMap R C) z)

/-- 代数上のKoszul複体への比較は、Cの標準スカラー作用に一致する。 -/
@[reassoc] theorem algebraKoszulTensorIso_coefficient_scalar {n : ℕ} (z : Fin n → R) (c : C) :
    (koszulTensorModuleFunctor z).map (ModuleCat.ofHom (LinearMap.mulLeft R c)) ≫
      (algebraKoszulTensorIso (C := C) z).hom =
    (algebraKoszulTensorIso (C := C) z).hom ≫
      ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex _).map
        (c • 𝟙 (koszulComplex (algebraMap R C ∘ z))) := by
  let U := (ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℤ)
  let e := algebraBaseChangeTensorIso (C := C) (koszulComplex z)
  let b := baseChangeKoszulIso (algebraMap R C) z
  let α := (koszulTensorModuleFunctor z).map (ModuleCat.ofHom (LinearMap.mulLeft R c))
  have h0 : U.map (c • 𝟙 (baseChange (algebraMap R C) (koszulComplex z))) ≫ e.hom = e.hom ≫ α :=
    algebraBaseChangeTensorIso_coefficient_scalar (koszulComplex z) c
  have h0' : α ≫ e.inv = e.inv ≫ U.map (c • 𝟙 (baseChange (algebraMap R C) (koszulComplex z))) := by
    calc
      α ≫ e.inv = e.inv ≫ (e.hom ≫ α) ≫ e.inv := by simp
      _ = e.inv ≫ (U.map (c • 𝟙 _) ≫ e.hom) ≫ e.inv := by rw [← h0]
      _ = _ := by simp [Category.assoc]
  have hb : (c • 𝟙 _) ≫ b.hom = b.hom ≫ (c • 𝟙 _) := by simp
  have hb' := congrArg (fun f ↦ U.map f) hb
  simp only [Functor.map_comp] at hb'
  change α ≫ (e.inv ≫ U.map b.hom) = (e.inv ≫ U.map b.hom) ≫ U.map (c • 𝟙 _)
  rw [← Category.assoc, h0', Category.assoc, hb', Category.assoc]

/-- 係数制限は余鎖複体のホモロジーと自然に可換である。 -/
def restrictCochainHomologyIso (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor _ _ i ≅
    HomologicalComplex.homologyFunctor _ _ i ⋙ ModuleCat.restrictScalars (algebraMap R C) :=
  NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R C)))
    (fun f ↦ CategoryTheory.ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ i).map f)
      (ModuleCat.restrictScalars (algebraMap R C)))

/-- 通常のC上のKoszulホモロジーと、基底環R上のTorの実際の加群比較。 -/
def algebraKoszulTorComparison {n : ℕ} (z : Fin n → R) (hz : IsKoszulResolution z) (i : ℕ) :
    ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj
        ((koszulComplex (algebraMap R C ∘ z)).homology (-(i : ℤ))) :=
  (koszulTorComparison z hz i).app (ModuleCat.of R C) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso (algebraKoszulTensorIso z) ≪≫
    (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).app _

/-- Tor上の係数元の作用は、通常のC上のKoszulホモロジーのスカラー作用に一致する。 -/
@[reassoc] theorem algebraKoszulTorComparison_coefficient_scalar {n : ℕ}
    (z : Fin n → R) (hz : IsKoszulResolution z) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) i c ≫
      (algebraKoszulTorComparison (C := C) z hz i).hom =
    (algebraKoszulTorComparison (C := C) z hz i).hom ≫
      (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 ((koszulComplex (algebraMap R C ∘ z)).homology (-(i : ℤ)))) := by
  let U := ModuleCat.restrictScalars (algebraMap R C)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-(i : ℤ))
  let K := koszulComplex (algebraMap R C ∘ z)
  let α := (koszulTensorModuleFunctor z).map (ModuleCat.ofHom (LinearMap.mulLeft R c))
  let eT := (koszulTorComparison z hz i).app (ModuleCat.of R C)
  let eK := algebraKoszulTensorIso (C := C) z
  let q := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).app K
  have ht : torCoefficientScalarEndomorphism C
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) i c ≫ eT.hom =
      eT.hom ≫ H.map α := koszulTorComparison_coefficient_scalar z hz C i c
  have hk := congrArg (fun f ↦ H.map f) (algebraKoszulTensorIso_coefficient_scalar z c)
  simp only [Functor.map_comp] at hk
  have hq : H.map ((U.mapHomologicalComplex _).map (c • 𝟙 K)) ≫ q.hom =
      q.hom ≫ U.map (c • 𝟙 (K.homology (-(i : ℤ)))) := by
    have h := (restrictCochainHomologyIso (R := R) (C := C) (-(i : ℤ))).hom.naturality
      (c • 𝟙 K)
    change H.map ((U.mapHomologicalComplex _).map (c • 𝟙 K)) ≫ q.hom =
      q.hom ≫ U.map (HomologicalComplex.homologyMap (c • 𝟙 K) (-(i : ℤ))) at h
    simpa only [homologyMap_smul, HomologicalComplex.homologyMap_id] using h
  change torCoefficientScalarEndomorphism C
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) i c ≫
      (eT.hom ≫ H.map eK.hom ≫ q.hom) =
    (eT.hom ≫ H.map eK.hom ≫ q.hom) ≫ U.map (c • 𝟙 (K.homology (-(i : ℤ))))
  rw [reassoc_of% ht, reassoc_of% hk, hq]
  simp only [Category.assoc]
  rfl

end SerrePositivity
