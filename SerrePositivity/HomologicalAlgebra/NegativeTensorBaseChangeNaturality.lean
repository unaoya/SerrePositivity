module
public import SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChange
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChangeNaturality
public import SerrePositivity.EInfinity.NegativeTensor.Naturality

/-!
概要：指定負次数テンソル底変換の比較が二つの鎖写像に自然であることを示す。
方針：零延長、負次数テンソル、底変換の既存の自然性を順に合成する。
規約：既存の比較同型を保ち、射を自然性が自明になるよう再定義しない。
使われ方：HA 1.2.4、G10 の全単体パラメータの EZ 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

/-- 同じ負次数テンソル底変換同型の両因子についての自然性。 -/
theorem negativeTensorBaseChangeIso_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    extendMap (((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).map
        (HomologicalComplex.tensorHom f g)) ComplexShape.embeddingDownNat ≫
        (negativeTensorBaseChangeIso φ K' L').hom =
      (negativeTensorBaseChangeIso φ K L).hom ≫ HomologicalComplex.tensorHom
        (extendMap (((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).map f)
          ComplexShape.embeddingDownNat)
        (extendMap (((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).map g)
          ComplexShape.embeddingDownNat) := by
  let F := ModuleCat.extendScalars φ
  let e := ComplexShape.embeddingDownNat
  have h0 := (mapExtendNatIso F e).inv.naturality (HomologicalComplex.tensorHom f g)
  have h1 := congrArg ((F.mapHomologicalComplex (.up ℤ)).map)
    (EInfinity.NegativeTensor.comparison_natural f g)
  simp only [Functor.map_comp] at h1
  have h2 := cochainTensorBaseChangeIso_naturality φ (extendMap f e) (extendMap g e)
  have hf := (mapExtendNatIso F e).hom.naturality f
  have hg := (mapExtendNatIso F e).hom.naturality g
  dsimp only [negativeTensorBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_hom]
  simp only [Category.assoc]
  erw [reassoc_of% h0]
  erw [reassoc_of% h1]
  erw [reassoc_of% h2]
  congr 1
  congr 1
  congr 1
  change HomologicalComplex.tensorHom _ _ ≫ HomologicalComplex.tensorHom _ _ =
    HomologicalComplex.tensorHom _ _ ≫ HomologicalComplex.tensorHom _ _
  erw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  exact congrArg₂ (fun a b => a ⊗ₘ b) hf hg

end SerrePositivity.HomologicalAlgebra
