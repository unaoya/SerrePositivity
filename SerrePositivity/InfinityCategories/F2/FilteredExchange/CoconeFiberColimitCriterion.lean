module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeFiberHomComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeTransformationEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.UnstraighteningMappingEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomInitiality

/-!
概要：元の余錐の全空間から fiber への写像の弱同値性から native な余極限性を導く。
方針：全 Hom の標準比較を実際の相対合成へ移し、輸送作用と前合成の同値性を使う。
規約：元の余錐そのものの余極限性を結論する。
使われ方：全空間の単位を実現した coherent 余錐の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 概要：元の fiber 写像の全 fiber 標的への前合成が同値なら元の余錐は余極限。
方針：元の全 Hom の族を同値な共通模型へ移し、元の fiber 写像による前合成へ比較する。
規約：底は任意で、filtered 性も余極限性も仮定しない。 -/
lemma isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence (c : JoinCocone F)
    (hc : ∀ z : SpaceInfinity.{u} _⦋0⦌, IsSimplicialHomotopyEquivalence
      ((pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z))) :
    IsColimitCone c := by
  let q (z : SpaceInfinity.{u} _⦋0⦌) := coconeTransformationMap F z ≫
    leftUnstraighteningMappingSpaceMap F (SSet.const z) ≫
      (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom
  have hq (z : SpaceInfinity.{u} _⦋0⦌) : IsSimplicialHomotopyEquivalence (q z) := by
    have h := (coconeTransformationMap_isQCatEquivalence F z).comp
      ((leftUnstraighteningMappingSpaceMap_isQCatEquivalence F (SSet.const z)).comp
        (qCatEquivalenceOfIso
          (constantUnstraighteningRelativeIso
            (leftUnstraighteningProjection F) z)).isQCatEquivalence)
    exact h.isSimplicialHomotopyEquivalence
  apply isColimitCone_of_pointHomFamily_comparison c
    (fun z ↦ (ihom (leftUnstraightening F)).obj (vertexFiber pointedSpaceProjection z)) q hq
  intro z
  have e := (coconePointHomNativeCompositionIso c z).postcomp
    (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom
  have he : FunctorIso (coconePointHomFamily c z ≫ q z)
      (coconePointHomRelativeComposite c z ≫
        (constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom) := by
    simpa only [q, Category.assoc] using e
  have h := (coconeFiberHomComparison_of_pre c z (hc z)).isQCatEquivalence
  exact (h.ofFunctorIso he.symm).isSimplicialHomotopyEquivalence

/-- 概要：元の余錐の実際の fiber 写像が弱同値なら元の余錐は余極限。
方針：必要な fiber 標的への前合成同値を回収し、元の全 Hom の判定を使う。
規約：元の全空間の Kan 性は不要。使われ方：弱同値による余極限の十分条件。 -/
lemma isColimitCone_of_coconeFiberMap_weakEquivalence (c : JoinCocone F)
    (hc : IsWeakHomotopyEquivalence (coconeFiberMap c)) : IsColimitCone c :=
  isColimitCone_of_coconeFiberMap_pre_homotopyEquivalence c (fun z ↦
    pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence
      (coconeFiberMap c) hc (vertexFiber pointedSpaceProjection z))

end SerrePositivity.InfinityCategories.F2
