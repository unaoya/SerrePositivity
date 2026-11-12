module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCriterion

/-!
概要：元の豊穣作用と同じ成分の商上の Hom 作用から、ε 整合圏への着地を構成する。
方針：各 Hom の pullback への持ち上げを束ね、単位・合成を単射包含で反映する。
規約：商上の Hom 作用の単位・合成を新たな入力として要求しない。
使われ方：D-S の resolved 作用の着地と、ε 整合圏の横合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (S : Set C) (T : Set D)
  (X : Type t) [DGCategory R X] (H : DGFunctor R X (DGFunctor R C D))
  (hH : ∀ x : X, ∀ c ∈ S, (H.obj x).obj c ∈ T)
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 元の同じ関手値に null 保存だけを添えた対象族。 -/
def quotientEpsilonFamilyObject (x : X) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T :=
  ⟨H.obj x, hH x⟩

variable
  (v : ∀ x y : X, homObject R X x y ⟶
    dgFunctorHom R _ _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T (quotientEpsilonFamilyObject R C D S T X H hH x))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T (quotientEpsilonFamilyObject R C D S T X H hH y)))
  (hv : ∀ x y : X,
    H.map x y ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents R C D S T
      (quotientEpsilonFamilyObject R C D S T X H hH x)
      (quotientEpsilonFamilyObject R C D S T X H hH y) =
    v x y ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents R C D S T
      (quotientEpsilonFamilyObject R C D S T X H hH x)
      (quotientEpsilonFamilyObject R C D S T X H hH y))

/-- 全 Hom の同じ成分の延長から、ε 整合関手圏への豊穣着地を作る。 -/
def nullPreservingFunctorsεLiftOfComponents :
    DGFunctor R X (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) where
  obj := quotientEpsilonFamilyObject R C D S T X H hH
  map x y := pullback.lift (H.map x y) (v x y) (hv x y)
  map_id x := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _)).mp
    change (eId (Complex R) x ≫ pullback.lift (H.map x x) (v x x) (hv x x)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _ = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonIdentity R C D S T _ ≫ _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonIdentity_ι]
    simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι, pullback.lift_fst]
    exact H.map_id x
  map_comp x y z := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _)).mp
    change (eComp (Complex R) x y z ≫
        pullback.lift (H.map x z) (v x z) (hv x z)) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _ =
      ((pullback.lift (H.map x y) (v x y) (hv x y) ⊗ₘ
        pullback.lift (H.map y z) (v y z) (hv y z)) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonComposition R C D S T _ _ _) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonComposition_ι]
    simp only [tensorHom_comp_tensorHom_assoc,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι, pullback.lift_fst]
    exact H.map_comp x y z

@[reassoc (attr := simp)]
lemma nullPreservingFunctorsεLiftOfComponents_map_ι (x y : X) :
    (nullPreservingFunctorsεLiftOfComponents R C D S T X H hH v hv).map x y ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T _ _ = H.map x y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma nullPreservingFunctorsεLiftOfComponents_map_extension (x y : X) :
    (nullPreservingFunctorsεLiftOfComponents R C D S T X H hH v hv).map x y ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T _ _ = v x y :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
