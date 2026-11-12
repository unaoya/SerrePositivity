module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionConstantEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConstantDiagramTransportCoordinates
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：元の定値標的の指定相対終点比較を、同じ実終点の指定 fiber 比較へ値まで戻す。
方針：両比較を同じ可縮な全延長空間の同じ終点評価での像へ同定する。
規約：二つの実延長と指定比較を保持。使われ方：元の三角形比較と輸送比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値標的の指定相対比較の fiber 表示は、同じ実延長の指定 fiber 比較と同じ値。 -/
lemma relativeExtensionConstantEndpoint_witnessIso_heq_fiber {A D C L : SSet.{u + 1}}
    (b : A ⟶ SpaceInfinity.{u}) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ PointedSpaceInfinity.{u}) (hv : v ≫ pointedSpaceProjection = i ≫ b)
    (j : C ⟶ A) (a : C ⟶ L) (z : SpaceInfinity.{u} _⦋0⦌)
    (hj : j ≫ b = a ≫ (SSet.const z : L ⟶ SpaceInfinity))
    (W₀ W₁ : A ⟶ PointedSpaceInfinity.{u})
    (h₀ : W₀ ≫ pointedSpaceProjection = b) (h₁ : W₁ ≫ pointedSpaceProjection = b)
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v)
    (g₀ g₁ : C ⟶ leftUnstraightening (SSet.const z : L ⟶ SpaceInfinity))
    (hg₀ : g₀ ≫ leftUnstraighteningProjection (SSet.const z) = a)
    (hg₁ : g₁ ≫ leftUnstraighteningProjection (SSet.const z) = a)
    (hj₀ : j ≫ W₀ = g₀ ≫ pullback.fst pointedSpaceProjection (SSet.const z))
    (hj₁ : j ≫ W₁ = g₁ ≫ pullback.fst pointedSpaceProjection (SSet.const z)) :
    HEq (VertexIso.map
      (relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection b i hi v hv j
        (SSet.const z) a hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hg₀ hg₁ hj₀ hj₁)
      (constantUnstraighteningRelativeIso a z).hom)
      (relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection b i hi v hv j z
        (hj.trans (SSet.comp_const a z)) W₀ W₁ h₀ h₁ hi₀ hi₁
        (g₀ ≫ constantUnstraighteningFiberProjection L z)
        (g₁ ≫ constantUnstraighteningFiberProjection L z)
        (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact hj₀)
        (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact hj₁)) := by
  have e := relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection b i hi v hv j
    (SSet.const z) a hj W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hg₀ hg₁ hj₀ hj₁
  have hs := (relativeFunctorExtensionEndpoint_vertex pointedSpaceProjection b i v hv j
    (SSet.const z) a hj W₀ h₀ hi₀ g₀ hg₀ hj₀).symm
  have ht := (relativeFunctorExtensionEndpoint_vertex pointedSpaceProjection b i v hv j
    (SSet.const z) a hj W₁ h₁ hi₁ g₁ hg₁ hj₁).symm
  refine (vertexIso_map_heq_of_heq _ _ hs ht e
    (constantUnstraighteningRelativeIso a z).hom).trans ?_
  refine (heq_of_eq (vertexIso_map_comp _ _ _)).trans ?_
  refine (vertexIso_map_heq _
    (relativeFunctorExtensionEndpoint_constant_fiber b i v hv j a z hj)).trans ?_
  exact (relativeExtensionFiberEndpoint_witnessIso_heq_map pointedSpaceProjection b i hi v hv j z
    (hj.trans (SSet.comp_const a z)) W₀ W₁ h₀ h₁ hi₀ hi₁
    (g₀ ≫ constantUnstraighteningFiberProjection L z)
    (g₁ ≫ constantUnstraighteningFiberProjection L z)
    (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact hj₀)
    (by rw [Category.assoc, constantUnstraighteningFiberProjection_ι]; exact hj₁)).symm

end SerrePositivity.InfinityCategories.F2
