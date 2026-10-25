module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrimitiveComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.Composition
/-!
概要：元終域の comma 比較の全 Hom 作用は元の dg 単位を保持する。
方針：同じ二射影と零比較 cochain を、comma Hom の三成分一意性へ渡す。
規約：元の gluing の単位を使い、比較 cochain を捨てない。
使われ方：元二脚を持つ dg comma 関手の構成に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
open KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
variable (X : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
lemma dgGluingHomTargetCommaHomMap_identity :
    dgGluingIdentity R C D (dgHomGluingBimodule R C D E p q) X ≫ dgGluingHomTargetCommaHomMap R C
        D E p q X X =
      dgFunctorCommaIdentity R D E q (dgGluingHomTargetCommaObject R C D E p q X) := by
  apply dgFunctorCommaHom_ext R D E q (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q X) _
  · rw [Category.assoc, dgGluingHomTargetCommaHomMap_source,
      dgGluingIdentity_right, dgFunctorCommaIdentity_source]
    rfl
  · rw [Category.assoc, dgGluingHomTargetCommaHomMap_replacement, ← Category.assoc,
      dgGluingIdentity_left, p.map_id, dgFunctorCommaIdentity_replacement]
    rfl
  · rw [dgFunctorCommaHomComparison_precompose,
      dgGluingHomTargetCommaHomMap_comparison, dgFunctorCommaIdentity_comparison]
    exact dgGluingIdentity_comparison R C D (dgHomGluingBimodule R C D E p q) X
end SerrePositivity.InfinityCategories
