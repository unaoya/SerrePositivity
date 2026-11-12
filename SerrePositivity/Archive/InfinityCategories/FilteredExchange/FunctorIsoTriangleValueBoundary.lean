module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：三つの実辺の値比較と元の指定三角形同型を、一つの境界比較へ束ねる。
方針：同じ三頂点の結合だけを揃え、最後辺・第一辺・指定三角形・長辺逆の順に合成する。
規約：指定四因子を保持。使われ方：普遍三角形残余の値の照合の明示した目標。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A B C X Y Z : SSet.{u}}
  (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (v₀ : A ⟶ X) (v₁ : B ⟶ Y) (v₂ : C ⟶ Z)
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
  (e₀₁ : FunctorIso (a ≫ v₁) (v₀ ≫ f)) (e₁₂ : FunctorIso (b ≫ v₂) (v₁ ≫ g))
  (e₀₂ : FunctorIso (d ≫ v₂) (v₀ ≫ h)) (τ : FunctorIso h (f ≫ g))

/-- 元の三辺の指定比較と同じ三角形同型から得る、同じ実二辺・長辺の値の境界比較。 -/
def functorIsoTriangleValueBoundary : FunctorIso ((a ≫ b) ≫ v₂) (d ≫ v₂) :=
  functorIsoOfEq (e₁₂.precomp a) (Category.assoc a b v₂).symm
      (Category.assoc a v₁ g).symm ≪≫
    functorIsoOfEq (e₀₁.postcomp g) rfl (Category.assoc v₀ f g) ≪≫
      (FunctorIso.precomp τ.symm v₀) ≪≫ e₀₂.symm

/-- 同じ境界比較を長辺の指定比較へ続けると、元の三つの指定因子だけが残る。 -/
lemma functorIsoTriangleValueBoundary_long_cancel :
    functorIsoTriangleValueBoundary a b d v₀ v₁ v₂ f g h e₀₁ e₁₂ e₀₂ τ ≪≫ e₀₂ =
      functorIsoOfEq (e₁₂.precomp a) (Category.assoc a b v₂).symm
        (Category.assoc a v₁ g).symm ≪≫
      functorIsoOfEq (e₀₁.postcomp g) rfl (Category.assoc v₀ f g) ≪≫
        FunctorIso.precomp τ.symm v₀ := by
  simp only [functorIsoTriangleValueBoundary, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end SerrePositivity.InfinityCategories.F2
