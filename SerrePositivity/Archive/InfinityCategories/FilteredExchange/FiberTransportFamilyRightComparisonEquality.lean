module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyRightComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberDataEquality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：元の二輸送の右結合 prism の指定比較を、既存の同じ endpointIso へ厳密に戻す。
方針：結合子の逆で全延長空間を制限し、元の底・初期値・実 prism を等式で揃える。
規約：指定比較を保持。使われ方：元の unstraightening 比較と輸送比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の二輸送の右結合 prism の指定比較は、元の endpointIso と厳密に一致する。 -/
lemma fiberTransportFamilyRightComparison_eq_endpointIso {E B K L : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) :
    fiberTransportFamilyRightComparison p f γ h₁ T U = T.endpointIso p f γ h₁ U := by
  have hs : (scaffoldFirstVertex 1 ▷ (K ⊗ L)) ≫ (α_ Δ[1] K L).inv =
      snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫ (prismEndpoint 0 K ▷ L) := by
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    change snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫
      prismEndpoint 0 (K ⊗ L) ≫ (α_ Δ[1] K L).inv = _
    rw [prismEndpoint_associator_inv]
  have hsj : prismEndpoint 1 (K ⊗ L) ≫ (α_ Δ[1] K L).inv = prismEndpoint 1 K ▷ L := by
    rw [prismEndpoint_associator_inv]
  unfold fiberTransportFamilyRightComparison
  refine (relativeExtensionFiberEndpoint_witnessIso_restriction p
    (fiberTransportFamilyRightBase K γ) (prismEndpoint 0 K ▷ L)
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne K) L)
    (fst K L ≫ f ≫ vertexFiberι p a) (fiberTransportFamilyRightComparison_initial p f γ T)
    (α_ Δ[1] K L).inv (snd Δ[0] (K ⊗ L)) (scaffoldFirstVertex 1 ▷ (K ⊗ L))
    (simplexPrismFirstVertex_leftAnodyne 1 (K ⊗ L)) hs (prismEndpoint 1 K ▷ L)
    (prismEndpoint 1 (K ⊗ L)) hsj b (fiberTransportFamilyRightComparison_final γ h₁)
    (fiberTransportFamilyRightPrism T) (fiberTransportFamilyRightPrism U)
    (fiberTransportFamilyRightPrism_projection T) (fiberTransportFamilyRightPrism_projection U)
    (fiberTransportFamilyRightPrism_source T) (fiberTransportFamilyRightPrism_source U)
    T.endpoint U.endpoint (fiberTransportFamilyRightPrism_target T)
    (fiberTransportFamilyRightPrism_target U)).trans ?_
  unfold FiberTransportFamily.endpointIso
  dsimp only
  apply relativeExtensionFiberEndpoint_witnessIso_eq_of_dataEq
  · simp only [fiberTransportFamilyRightBase, Iso.inv_hom_id_assoc]
  · rfl
  · simp only [fiberTransportFamilyRightPrism, Iso.inv_hom_id_assoc]
  · simp only [fiberTransportFamilyRightPrism, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2
