module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFaceComparison
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionDataEndpoint

/-!
概要：元の単位三単体の面の選択空間を、元の指定二単体の選択空間へ揃える。
方針：厳密な底の等式と初期値の等式で、実延長を変えずに同型を作る。
規約：同じ全空間と同じ始点を保持。使われ方：共有面の指定比較を同じ空間で消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  (S : (Δ[2] : SSet.{u + 1}) ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S)

include hj hS in
/-- 同じ零頂点を含む元の指定二面は、全底上でも元の始域図式を始点に持つ。 -/
lemma coherentColimitUnitPointedFace_initial :
    simplexPrismVertex 2 0 ((SSet.uliftFunctor.{u + 1, u}).obj B) ≫
      functorSimplexDiagram S = F := by
  apply functorSimplexDiagram_initial
  have hs : stdSimplex.δ j ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = S := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact hS
  rw [← hs, ← Category.assoc, tetrahedronFace_initial j hj]
  exact coherentColimitUnitTriangleTetrahedron_initial B T k

/-- 元の全二面の実延長を保持して、元の指定二単体の選択空間へ底と初期値を揃える。 -/
def coherentColimitUnitPointedFaceIso :
    coherentColimitUnitPointedTetrahedronFaceChoice B T k j hj ≅
      leftUnstraighteningSimplexChoiceSpace F 2 (functorSimplexDiagram S)
        (coherentColimitUnitPointedFace_initial B T k j hj S hS) :=
  relativeExtensionDataIso pointedSpaceProjection _ _ (scaffoldFirstVertex 2 ▷ _)
    (𝟙 _ ≫ leftUnstraighteningSimplexStart F) (leftUnstraighteningSimplexStart F) _
    (leftUnstraighteningSimplexStart_projection F 2 _
      (coherentColimitUnitPointedFace_initial B T k j hj S hS))
    (coherentColimitUnitPointedTetrahedronDiagram_face_base B T k j S hS)
    (Category.id_comp _)

/-- 元の全三単体から元の指定二単体への制限。全実延長を変えない底の正規化を含む。 -/
def coherentColimitUnitPointedFaceMap :
    coherentColimitUnitPointedTetrahedronChoice B T k ⟶
      leftUnstraighteningSimplexChoiceSpace F 2 (functorSimplexDiagram S)
        (coherentColimitUnitPointedFace_initial B T k j hj S hS) :=
  coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj ≫
    (coherentColimitUnitPointedFaceIso B T k j hj S hS).hom

/-- 底の正規化を含む制限でも、選択済みの元の持ち上げの全二面は厳密に保持される。 -/
lemma coherentColimitUnitPointedFace_vertex :
    (((coherentColimitUnitPointedFaceMap B T k j hj S hS).app (Opposite.op ⦋0⦌)
      (coherentColimitUnitPointedTetrahedronChoice_vertex B T k)).val).val =
      functorVertex ((stdSimplex.δ j ▷ leftUnstraightening F) ≫
        coherentColimitUnitPointedTetrahedron B T k) := by
  exact coherentColimitUnitPointedTetrahedronFaceRestriction_vertex B T k j hj

end SerrePositivity.InfinityCategories.F2
