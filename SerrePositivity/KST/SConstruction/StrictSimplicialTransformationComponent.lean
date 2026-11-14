module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve

/-! # 厳密単体的自然変換の元の通常成分の回収
概要：単位からの豊穣表示で指定した通常射を、coherent nerve の比較成分から回収する。
方針：元の零単体の同値の逆律を使う。
規約：成分そのものの等号。使われ方：Kan S₁ 比較の可逆辺判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 豊穣表示を指定した通常射は、同じ strict transformation の成分として回収される。 -/
lemma strictSimplicialTransformation_componentHom
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F G : EnrichedFunctor SSet.{u} C D)
    (τ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (X : C) (f : F.obj X ⟶ G.obj X) (h : τ.app X = eHomEquiv SSet f) :
    Spectra.StrictEnrichedTransformation.componentHom F G τ X = f := by
  apply (SimplicialCategory.homEquiv' _ _).injective
  change (SimplicialCategory.homEquiv' _ _)
    ((SimplicialCategory.homEquiv' _ _).symm _) = _
  rw [Equiv.apply_symm_apply]
  exact types_congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) PUnit.unit

end SerrePositivity.KST.SConstruction
