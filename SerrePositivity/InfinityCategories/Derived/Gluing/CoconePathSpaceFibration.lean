module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedChainMapFibration
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceContraction

/-! 複体の空間模型の全射性と、同じ cocone・path 射影の実 Kan fibration。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPinchedMap_fibration {K L : Complex R} (φ : K ⟶ L)
    (hs : ∀ k : ℤ, Function.Surjective (φ.f k)) :
    Fibration (complexPinchedMap.{u, v} φ) :=
  dgGluingPinchedChainMap_fibration _ (complexUnitHomPostcompose_surjective φ hs)

lemma dgGluingCoconeSpaceProjection_fibration {P Q : Complex R} (d : P ⟶ Q) :
    Fibration (complexPinchedMap.{u, v} (mappingCocone.fst d)) := by
  apply dgGluingComplexPinchedMap_fibration
  intro k y
  refine ⟨(mappingCocone.inl d).v k k (add_zero k) y, ?_⟩
  exact ConcreteCategory.congr_hom (mappingCocone.inl_v_fst_f d k) y

lemma dgGluingCoconePathSpaceProjection_fibration (Q : Complex R) :
    Fibration (complexPinchedMap.{u, v} (mappingCocone.fst (𝟙 Q))) :=
  dgGluingCoconeSpaceProjection_fibration _

end SerrePositivity.InfinityCategories
