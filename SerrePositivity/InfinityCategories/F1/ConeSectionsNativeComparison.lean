module

public import SerrePositivity.InfinityCategories.F1.ConeUnstraighteningMap
public import SerrePositivity.InfinityCategories.F1.ConstantDiagramSectionTransport
public import SerrePositivity.InfinityCategories.F1.ConePointHomComposition
public import SerrePositivity.InfinityCategories.F1.ConeSectionsHomAction

/-!
概要：元の native な錐の全 Hom 比較を、同じ全切断写像の全 Hom 作用と比較する。
方針：同じ三角形の相対合成を底上の後合成へ戻し、定値図式の輸送比較を続ける。
規約：元の錐・全 Hom・元の比較射を保持する。
使われ方：一般 coherent 小極限の native な普遍性の結論。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 同じ全 Hom の相対合成は、元の錐の底上の射による後合成そのもの。 -/
lemma conePointHomRelativeComposite_post (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    conePointHomRelativeComposite c z =
      (conePointHomFirstTransformation c z ≫
        leftUnstraighteningMappingSpaceMap (SSet.const z) (SSet.const c.vertex : B ⟶ _)) ≫
      HomotopyLimits.relativeFunctorPost
        (leftUnstraighteningProjection (SSet.const c.vertex : B ⟶ _))
        (leftUnstraighteningProjection F) (coneUnstraighteningArrow c).left
        (coneUnstraighteningArrow c).w (leftUnstraighteningProjection (SSet.const z : B ⟶ _)) := by
  apply relativeFunctorUncurry_injective
    (leftUnstraighteningProjection F) (leftUnstraighteningProjection (SSet.const z : B ⟶ _))
  rw [relativeFunctorPost_uncurry]
  have hd : relativeFunctorUncurry (conePointHomRelativeComposite c z) =
      lift (relativeFunctorUncurry (conePointHomFirstTransformation c z ≫
        leftUnstraighteningMappingSpaceMap (SSet.const z) (SSet.const c.vertex : B ⟶ _)))
        (snd (leftUnstraightening (SSet.const z : B ⟶ _)) (pinchedHom z c.vertex)) ≫
      relativeFunctorUncurry ((SSet.const (coneTransformationVertex c)) ≫
        leftUnstraighteningMappingSpaceMap (SSet.const c.vertex) F) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hd, coneUnstraighteningArrow_const_evaluation, ← Category.assoc, lift_fst]

/-- 元の native な全 Hom 比較の全切断への像は、同じ全切断写像の作用と同型。 -/
def coneSectionsNativeComparisonIso (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso ((fixedApexConeHomComparison c z ≫ coneTransformationMap F z) ≫
      coherentConstantSourceMap F z) (coneSectionsHomAction c z) := by
  have e := (conePointHomNativeCompositionIso c z).postcomp
    (constantUnstraighteningSourceRelativeIso F z).hom
  have e' := constantDiagramSectionTransportIso F (coneUnstraighteningArrow c).left
    (coneUnstraighteningArrow c).w (pinchedHomToIntervalMappingSpace z c.vertex)
  change FunctorIso (_ ≫ (constantUnstraighteningSourceRelativeIso F z).hom) _ at e'
  have hp := conePointHomRelativeComposite_post c z
  dsimp only [conePointHomFirstTransformation] at hp
  rw [← hp, ← coneSectionsMap_eq_sectionMap] at e'
  exact e ≪≫ e'

end SerrePositivity.InfinityCategories
