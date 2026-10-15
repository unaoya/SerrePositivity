module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import Mathlib.Algebra.Homology.Linear

/-! # 線形加法関手とスカラー作用の錐

加法関手の標準の錐比較を、写像の等式と自然変換に両立させる。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.homotopyCofiber
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 関手で移した射を指定の射と同一視した場合の、標準の錐比較。 -/
def additiveFunctorCofiberIsoOfEq (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ Q)
    (ψ : (F.mapHomologicalComplex _).obj P ⟶ (F.mapHomologicalComplex _).obj Q)
    (h : (F.mapHomologicalComplex _).map φ = ψ) :
    (F.mapHomologicalComplex _).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ψ :=
  mapHomologicalComplexObjIso φ F ≪≫ eqToIso (congrArg (fun f : (F.mapHomologicalComplex _).obj P ⟶
    (F.mapHomologicalComplex _).obj Q ↦ CochainComplex.mappingCone f) h)

@[reassoc (attr := simp)] theorem additiveFunctorCofiberIsoOfEq_inv_inl
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ Q)
    (ψ : (F.mapHomologicalComplex _).obj P ⟶ (F.mapHomologicalComplex _).obj Q)
    (h : (F.mapHomologicalComplex _).map φ = ψ) (i : ℤ) :
    inlX ψ (i + 1) i rfl ≫ (additiveFunctorCofiberIsoOfEq F φ ψ h).inv.f i =
      F.map (inlX φ (i + 1) i rfl) := by
  subst ψ
  simp [additiveFunctorCofiberIsoOfEq, mapHomologicalComplexObjIso]

@[reassoc (attr := simp)] theorem additiveFunctorCofiberIsoOfEq_inv_inr
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ Q)
    (ψ : (F.mapHomologicalComplex _).obj P ⟶ (F.mapHomologicalComplex _).obj Q)
    (h : (F.mapHomologicalComplex _).map φ = ψ) (i : ℤ) :
    inrX ψ i ≫ (additiveFunctorCofiberIsoOfEq F φ ψ h).inv.f i = F.map (inrX φ i) := by
  subst ψ
  simp [additiveFunctorCofiberIsoOfEq, mapHomologicalComplexObjIso]

/-- R線形な加法関手は、a作用の錐と可換である。 -/
def linearFunctorScalarConeIso (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (F.mapHomologicalComplex _).obj ((scalarConeFunctor a).obj K) ≅
      (scalarConeFunctor a).obj ((F.mapHomologicalComplex _).obj K) :=
  additiveFunctorCofiberIsoOfEq F (smulId a K)
    (smulId a ((F.mapHomologicalComplex _).obj K)) (by
      ext i
      simp [smulId])

/-- 錐比較は関手の間の任意の自然変換とも両立する。 -/
@[reassoc] theorem linearFunctorScalarConeIso_natTrans
    (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [G.Additive]
    [F.Linear R] [G.Linear R] (α : F ⟶ G) (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (NatTrans.mapHomologicalComplex α _).app ((scalarConeFunctor a).obj K) ≫
      (linearFunctorScalarConeIso G a K).hom =
    (linearFunctorScalarConeIso F a K).hom ≫
      (scalarConeFunctor a).map ((NatTrans.mapHomologicalComplex α _).app K) := by
  rw [← cancel_epi (linearFunctorScalarConeIso F a K).inv,
    ← cancel_mono (linearFunctorScalarConeIso G a K).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext i
  apply ext_from_X (smulId a ((F.mapHomologicalComplex _).obj K)) (i + 1) i rfl
  · simp only [linearFunctorScalarConeIso, HomologicalComplex.comp_f,
      scalarConeFunctor_inl_map_assoc, additiveFunctorCofiberIsoOfEq_inv_inl_assoc,
      additiveFunctorCofiberIsoOfEq_inv_inl]
    exact α.naturality (inlX (smulId a K) (i + 1) i rfl)
  · simp only [linearFunctorScalarConeIso, HomologicalComplex.comp_f,
      scalarConeFunctor_inr_map_assoc, additiveFunctorCofiberIsoOfEq_inv_inr_assoc,
      additiveFunctorCofiberIsoOfEq_inv_inr]
    exact α.naturality (inrX (smulId a K) i)

end SerrePositivity
