module
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-!
概要：直和を保つ加法的閉関手について、行有限行列の端点同型付き可換性を束ねる。
方針：余積包含で射を検出し、各行の有限和と元の端点比較を照合する。
規約：行列全体の実射の等式を得る。
使われ方：c′ の自由 sphere 行列の実延長比較を全直和へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable {C : Type v} {E : Type w} [Category C] [Category E]

def coproductFamilyImageIso {I : Type u} [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    (F : C ⥤ E) (A : I → C) (B : I → E)
    [PreservesColimit (Discrete.functor A) F] (e : ∀ i, F.obj (A i) ≅ B i) :
    F.obj (∐ A) ≅ ∐ B :=
  PreservesCoproduct.iso F A ≪≫ Sigma.mapIso e

lemma coproductFamilyImageIso_ι {I : Type u}
    [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    (F : C ⥤ E) (A : I → C) (B : I → E)
    [PreservesColimit (Discrete.functor A) F] (e : ∀ i, F.obj (A i) ≅ B i) (i : I) :
    F.map (Sigma.ι A i) ≫ (coproductFamilyImageIso F A B e).hom =
      (e i).hom ≫ Sigma.ι B i := by
  have h := (isColimitOfHasCoproductOfPreservesColimit F A).comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct (fun i => F.obj (A i))) ⟨i⟩
  change F.map (Sigma.ι A i) ≫ (PreservesCoproduct.iso F A).hom = _ at h
  simp only [coproductFamilyImageIso, Iso.trans_hom, ← Category.assoc]
  rw [h]
  change Sigma.ι (fun i => F.obj (A i)) i ≫ (Sigma.mapIso e).hom = _
  exact Sigma.ι_mapIso_hom e i

lemma coproductFamilyImageIso_matrix [Preadditive C] [Preadditive E]
    {I J : Type u} [HasCoproductsOfShape I C] [HasCoproductsOfShape I E]
    [HasCoproductsOfShape J C] [HasCoproductsOfShape J E]
    (F : C ⥤ E) [F.Additive] (A : I → C) (B : J → C) (A' : I → E) (B' : J → E)
    [PreservesColimit (Discrete.functor A) F] [PreservesColimit (Discrete.functor B) F]
    (a : ∀ i, F.obj (A i) ≅ A' i) (b : ∀ j, F.obj (B j) ≅ B' j)
    (s : I → Finset J) (g : ∀ i j, A i ⟶ B j) (f : ∀ i j, A' i ⟶ B' j)
    (h : ∀ i j, j ∈ s i → F.map (g i j) ≫ (b j).hom = (a i).hom ≫ f i j) :
    F.map (Sigma.desc (fun i => ∑ j ∈ s i, g i j ≫ Sigma.ι B j)) ≫
      (coproductFamilyImageIso F B B' b).hom =
    (coproductFamilyImageIso F A A' a).hom ≫
      Sigma.desc (fun i => ∑ j ∈ s i, f i j ≫ Sigma.ι B' j) := by
  classical
  apply (isColimitOfHasCoproductOfPreservesColimit F A).hom_ext
  rintro ⟨i⟩
  change F.map (Sigma.ι A i) ≫ _ = F.map (Sigma.ι A i) ≫ _
  rw [← F.map_comp_assoc, Sigma.ι_desc]
  rw [← Category.assoc, coproductFamilyImageIso_ι, Category.assoc, Sigma.ι_desc]
  simp only [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum,
    F.map_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coproductFamilyImageIso_ι, ← Category.assoc, h i j hj]
  simp only [Category.assoc]

end SerrePositivity.DifferentialGraded
