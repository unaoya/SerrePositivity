module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCategory
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPostcomposition

/-!
概要：ε 整合 Hom 部分複体の包含を、固定 ε の全次数整合と同値にする。
方針：商延長の必要十分条件と pullback の普遍性を任意複体パラメータで適用する。
規約：pullback の第二成分は一意であり、新たな延長選択を入力に残さない。
使われ方：D-S の resolvedInputFunctor が同じ ε 整合 Hom に入ることの判定。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (S : Set C) (T : Set D)
  (F G : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) {K : Complex R}
local instance : HasProductsOfShape C (ModuleCat.{u} R) := ModuleCat.hasLimitsOfShape

/-- 正本商関手と同じ、標的商の元の ε を指定した収縮付き関手。 -/
def quotientEpsilonContracted (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    DGQuotient.ContractedFunctor R C S (DGQuotient.QuotientObject D T) :=
  DGQuotient.functorContracted R C D F.val S T F.property

/-- 元 Hom の任意複体パラメータを、同じ標的商への包含で写す。 -/
def quotientEpsilonOriginalParameter (u : K ⟶ dgFunctorHom R C D F.val G.val) :
    DGFunctorParamTrans R C (DGQuotient.QuotientObject D T) K
      (quotientEpsilonContracted R C D S T F).toDGFunctor
      (quotientEpsilonContracted R C D S T G).toDGFunctor :=
  dgFunctorParamPost R C D (DGQuotient.QuotientObject D T) (DGQuotient.inclusion R D T)
    (dgFunctorHomEquiv R C D K F.val G.val u)

lemma quotientEpsilonOriginalParameter_app
    (u : K ⟶ dgFunctorHom R C D F.val G.val) (x : C) :
    (quotientEpsilonOriginalParameter R C D S T F G u).app x =
      u ≫ dgFunctorHomπ R C D F.val G.val x ≫
        (DGQuotient.inclusion R D T).map (F.val.obj x) (G.val.obj x) :=
  Category.assoc _ _ _

/-- 元 Hom の全次数パラメータが固定 ε と整合するという正確な条件。 -/
def quotientEpsilonCompatible (u : K ⟶ dgFunctorHom R C D F.val G.val) : Prop :=
  ∀ (b : S) (k : ℤ) (t : K.X k),
    forward R ((quotientEpsilonContracted R C D S T F).homotopy b)
        (((quotientEpsilonOriginalParameter R C D S T F G u).app b.val).f k t) rfl =
      (k * (-1)).negOnePow • forward R
        (((quotientEpsilonOriginalParameter R C D S T F G u).app b.val).f k t)
        ((quotientEpsilonContracted R C D S T G).homotopy b) (by omega)

/-- 固定 ε に整合する元の全パラメータを、Hom 部分複体へ一意に持ち上げる。 -/
def quotientEpsilonHomLift (u : K ⟶ dgFunctorHom R C D F.val G.val)
    (hε : quotientEpsilonCompatible R C D S T F G u) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G := by
  let σ := DGQuotient.parameterExtension R
    (quotientEpsilonContracted R C D S T F) (quotientEpsilonContracted R C D S T G)
    (quotientEpsilonOriginalParameter R C D S T F G u) hε
  refine pullback.lift u ((dgFunctorHomEquiv R _ _ K
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T G)).symm σ) ?_
  apply Pi.hom_ext
  intro x
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalComponents_π,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonExtendedComponents_π, dgFunctorHomEquiv_symm_π]
  change u ≫ dgFunctorHomπ R C D F.val G.val x ≫
    (DGQuotient.inclusion R D T).map (F.val.obj x) (G.val.obj x) =
      (quotientEpsilonOriginalParameter R C D S T F G u).app x
  exact (quotientEpsilonOriginalParameter_app R C D S T F G u x).symm

@[reassoc (attr := simp)]
lemma quotientEpsilonHomLift_ι (u : K ⟶ dgFunctorHom R C D F.val G.val)
    (hε : quotientEpsilonCompatible R C D S T F G u) :
    quotientEpsilonHomLift R C D S T F G u hε ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G = u :=
  pullback.lift_fst _ _ _

/-- Hom 部分複体内の全パラメータは、同じ元の成分で固定 ε と整合する。 -/
lemma quotientEpsilonHomι_compatible (ρ : K ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G) :
    quotientEpsilonCompatible R C D S T F G (ρ ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G) := by
  apply DGQuotient.parameterExtension_epsilon_necessary R
    (quotientEpsilonContracted R C D S T F) (quotientEpsilonContracted R C D S T G)
    (quotientEpsilonOriginalParameter R C D S T F G _)
    (dgFunctorHomEquiv R _ _ K (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T F)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonObject R C D S T G) (ρ ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F G))
  intro x
  change (ρ ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension R C D S T F G) ≫
    dgFunctorHomπ R _ _ _ _ ⟨x⟩ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomExtension_π, quotientEpsilonOriginalParameter_app]
  simp only [Category.assoc]

/-- 部分複体への包含は、任意複体パラメータの固定 ε 整合と同値である。 -/
theorem quotientEpsilonHom_factor_iff (u : K ⟶ dgFunctorHom R C D F.val G.val) :
    (∃ ρ : K ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C D S T F G,
      ρ ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C D S T F G = u) ↔
        quotientEpsilonCompatible R C D S T F G u := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact quotientEpsilonHomι_compatible R C D S T F G ρ
  · intro hε
    exact ⟨quotientEpsilonHomLift R C D S T F G u hε,
      quotientEpsilonHomLift_ι R C D S T F G u hε⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
