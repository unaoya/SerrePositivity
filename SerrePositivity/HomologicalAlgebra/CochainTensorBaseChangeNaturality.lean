module
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange

/-!
概要：既存のテンソル底変換同型の両複体に対する自然性を証明する。
方針：全次数の標準余積包含で検出し、係数拡大のテンソル比較の自然性に帰着する。
規約：既存の cochainTensorBaseChangeIso を保持し、置き換えない。
使われ方：HA 1.2.4、G10 の負次数 EZ 比較の全パラメータ自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
open CategoryTheory.Functor.OplaxMonoidal
namespace SerrePositivity.HomologicalAlgebra
variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

/-- 指定テンソル底変換同型は両因子の実鎖写像に自然。 -/
@[reassoc]
theorem cochainTensorBaseChangeIso_naturality
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.tensorHom f g) ≫ (cochainTensorBaseChangeIso φ P' Q').hom =
      (cochainTensorBaseChangeIso φ P Q).hom ≫ HomologicalComplex.tensorHom
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map f)
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply cochainTensorBaseChange_hom_ext φ P Q
  intro i j h
  change (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n h) ≫
      (ModuleCat.extendScalars φ).map ((HomologicalComplex.tensorHom f g).f n) ≫
      (cochainTensorBaseChangeXIso φ P' Q' n).hom =
    (ModuleCat.extendScalars φ).map (ιTensorObj P Q i j n h) ≫
      (cochainTensorBaseChangeXIso φ P Q n).hom ≫ _
  rw [← Functor.map_comp_assoc, ιTensorObj_cochainTensorMap, Functor.map_comp,
    Category.assoc, map_ι_cochainTensorBaseChangeXIso,
    map_ι_cochainTensorBaseChangeXIso_assoc, ιTensorObj_cochainTensorMap]
  rw [← δ_natural_assoc]
  rfl

end SerrePositivity.HomologicalAlgebra
