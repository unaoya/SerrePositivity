module

public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTransformationRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Stable.InitialTransport
public import SerrePositivity.InfinityCategories.Stable.ColimitRestriction
public import SerrePositivity.InfinityCategories.Stable.ColimitCoconeFamily

/-!
概要：指定図式での Kan 普遍性を native な余錐の制限へ移す。
方針：全写像空間の同値を区間模型、終点固定余錐、全余錐の順に移す。
規約：添字の cofinal 性や制限関手全体の充満忠実性を仮定しない。
使われ方：同じ相対 join 族に沿う native な Kan 合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定図式での相対始点境界充填は、同じ定値標的への全変換の制限を同値にする。 -/
lemma constantTransformationRestriction_isQCatEquivalence_of_initialBoundary
    {K L X : SSet.{u}} [Quasicategory X] (f : K ⟶ X) (i : L ⟶ K)
    (hf : InitialBoundaryLifting ((pre i).app X) (functorVertex f)) (z : X _⦋0⦌) :
    IsQCatEquivalence (constantTransformationRestriction i f z) := by
  have hp := (SerrePositivity.InfinityCategories.F1B.pinchedHomMap_equivalence_of_initialBoundary
    ((pre i).app X) (functorVertex f) (functorVertex (SSet.const z)) hf).isQCatEquivalence
  have he : ((pre i).app X).app _ (functorVertex (SSet.const z)) =
      functorVertex (SSet.const z) := by
    change functorVertex (i ≫ SSet.const z) = _
    rw [SSet.comp_const]
  have ht := hp.comp (qCatEquivalenceOfIso (eqToIso
    (congrArg₂ (fun a b => pinchedHom a b) (rfl :
      ((pre i).app X).app _ (functorVertex f) = functorVertex (i ≫ f)) he))).isQCatEquivalence
  have hh := ht.comp (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (functorVertex (i ≫ f)) (functorVertex (SSet.const z)))
  change IsQCatEquivalence ((pinchedHomMap ((pre i).app X) (functorVertex f)
    (functorVertex (SSet.const z)) ≫ eqToHom (congrArg₂ (fun a b => pinchedHom a b)
      (rfl : ((pre i).app X).app _ (functorVertex f) = functorVertex (i ≫ f)) he)) ≫
    pinchedHomToIntervalMappingSpace (functorVertex (i ≫ f))
      (functorVertex (SSet.const z))) at hh
  have hn := pinchedHomToIntervalMappingSpace_postOfEq ((pre i).app X)
    (functorVertex f) (functorVertex (SSet.const z))
    (rfl : ((pre i).app X).app _ (functorVertex f) = functorVertex (i ≫ f)) he
  have hh' : IsQCatEquivalence (pinchedHomToIntervalMappingSpace (functorVertex f)
      (functorVertex (SSet.const z)) ≫ constantTransformationRestriction i f z) := by
    unfold constantTransformationRestriction
    rw [← hn]
    exact hh
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (functorVertex f) (functorVertex (SSet.const z))).cancel_left hh'

/-- 同じ指定図式での相対普遍性は、終点固定 native 余錐空間の制限を同値にする。 -/
lemma cosliceRestrictionFiberMap_isQCatEquivalence_of_initialBoundary
    {K L X : SSet.{u}} [Quasicategory X] (f : K ⟶ X) (i : L ⟶ K)
    (hf : InitialBoundaryLifting ((pre i).app X) (functorVertex f)) (z : X _⦋0⦌) :
    IsQCatEquivalence (cosliceRestrictionFiberMap f i z) := by
  have hh := (F2.coconeTransformationMap_isQCatEquivalence f z).comp
    (constantTransformationRestriction_isQCatEquivalence_of_initialBoundary f i hf z)
  rw [← coconeTransformationMap_restrict i f z] at hh
  exact (F2.coconeTransformationMap_isQCatEquivalence (i ≫ f) z).cancel_right hh

/-- 同じ指定図式の native 全余錐空間の制限は相対始点境界充填から同値となる。 -/
lemma sliceUnderRestrict_isQCatEquivalence_of_initialBoundary
    {K L X : SSet.{u}} [Quasicategory X] (f : K ⟶ X) (i : L ⟶ K)
    (hf : InitialBoundaryLifting ((pre i).app X) (functorVertex f)) :
    IsQCatEquivalence (sliceUnderRestrict f i) := by
  apply isQCatEquivalence_of_leftFibration_fibers (sliceUnderProjection f)
    (sliceUnderProjection (i ≫ f)) (sliceUnderRestrict f i) rfl
  intro z
  exact cosliceRestrictionFiberMap_isQCatEquivalence_of_initialBoundary f i hf z

/-- 同じ全余錐の余極限性を、指定図式での Kan 普遍的な制限が検出する。 -/
lemma isColimitCone_iff_restrict_of_initialBoundary
    {K L X : SSet.{u}} [Quasicategory X] {f : K ⟶ X} (i : L ⟶ K)
    (hf : InitialBoundaryLifting ((pre i).app X) (functorVertex f)) (c : JoinCocone f) :
    IsColimitCone c ↔ IsColimitCone (c.restrict i) :=
  (sliceUnderRestrict_isQCatEquivalence_of_initialBoundary f i hf).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.F2.Ind
