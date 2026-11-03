module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceEndpointIso
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceOriginalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionWitnessComparison

/-!
概要：native 合成への終点比較は、構成済みの元の第零面の全族比較の同じ終点像である。
方針：二つの元の証拠を既存の終点比較の表示式に渡し、表示変更だけを除く。
規約：指定比較の値を保持。使われ方：六面の三関係を元の native 比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k
local notation "b₂" => ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  PointedTransportPrismFamily.diagram (coherentColimitUnitPointedZeroFaceFamily B T k)
local notation "i₂" => (scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K
local notation "j₂" => simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K

/-- native 合成への同じ指定終点比較は、元の全族比較を終点へ写した値そのもの。 -/
lemma coherentColimitUnitZeroFaceEndpointIso_heq_map :
    HEq (coherentColimitUnitZeroFaceEndpointIso B T k H he S hS)
      (VertexIso.map (coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS)
        (relativeFunctorExtensionEndpoint pointedSpaceProjection b₂ i₂ (D).boundary (D).projection
          j₂ Q₂ (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
          (coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS))) := by
  let w₀ := coherentColimitUnitZeroFaceEndpointWitness B T k H he S hS false
  let w₁ := coherentColimitUnitZeroFaceEndpointWitness B T k H he S hS true
  exact relativeExtensionEndpoint_witnessIso_heq_map pointedSpaceProjection b₂ i₂
    (leftAnodyneExtensions_whiskerRight _
      (simplexPrismFirstVertex_leftAnodyne 2 (leftUnstraightening F)) K)
    (D).boundary (D).projection j₂ Q₂
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS)
    w₀.extension w₁.extension w₀.over w₁.over w₀.initial w₁.initial
    w₀.endpoint w₁.endpoint w₀.endpoint_over w₁.endpoint_over w₀.evaluate w₁.evaluate

/-- 中央の元の第零面の実終点を、元の下単位三角形の native 合成へ結ぶ。 -/
def coherentColimitUnitMiddleZeroFaceEndpointIso :=
  coherentColimitUnitZeroFaceEndpointIso B T 1 l
    (coherentColimitUnitTetrahedron_middle_firstEdge B T)
    (coherentColimitUnitLowerTriangle B r) (coherentColimitUnitTetrahedron_upper_last B T)

/-- 最後の元の第零面の実終点を、元の上単位三角形の native 合成へ結ぶ。 -/
def coherentColimitUnitLastZeroFaceEndpointIso :=
  coherentColimitUnitZeroFaceEndpointIso B T 2 l
    (coherentColimitUnitTetrahedron_last_firstEdge B T)
    (coherentColimitUnitUpperTriangle B r) (coherentColimitUnitTetrahedron_lower_last B T)

end SerrePositivity.InfinityCategories.F2
