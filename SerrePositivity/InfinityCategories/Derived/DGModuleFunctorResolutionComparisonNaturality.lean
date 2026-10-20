module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionIdentity
/-!
概要：実比較 cochain の回収と、全パラメータからの前合成の両立。
方針：実成分ごとの合成の結合律を使う。使われ方：実単位律・結合律の比較成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y : DGModuleFunctorResolutionObject R C E F)
/-- 実比較 cochain の回収は、任意の実鎖写像による前合成と可換。 -/
lemma dgModuleFunctorResolutionHomComparison_precompose {K L : Complex R} (f : K ⟶ L)
    (g : L ⟶ dgModuleFunctorResolutionHomComplex R C E F X Y) :
    dgModuleFunctorResolutionHomComparison R C E F X Y K (f ≫ g) =
      (Cochain.ofHom f).comp
        (dgModuleFunctorResolutionHomComparison R C E F X Y L g) (zero_add (-1)) := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgModuleFunctorResolutionHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]
/-- 恒等鎖写像からは、同じ mapping cocone の実比較 cochain を回収する。 -/
lemma dgModuleFunctorResolutionHomComparison_id :
    dgModuleFunctorResolutionHomComparison R C E F X Y _ (𝟙 _) =
      dgModuleFunctorResolutionPrimitive R C E F X Y := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgModuleFunctorResolutionHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp]
  rfl
end SerrePositivity.InfinityCategories
