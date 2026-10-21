module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedTetrahedra
public import SerrePositivity.InfinityCategories.F2.TetrahedronFaceComparison

/-!
概要：元の単位三単体の pointed な選択空間を、同じ始点を持つ元の二面へ制限する。
方針：元の三単体の全図式と初期値を既存の面制限へ渡し、実際の制限頂点を回収する。
規約：元の全空間の全パラメータを保持。使われ方：指定三角形比較の共通選択空間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)

/-- 元の単位三単体の二面の展開は、その元の面図式の展開そのもの。 -/
lemma coherentColimitUnitPointedTetrahedronDiagram_face (j : Fin 4)
    (S : (Δ[2] : SSet.{u + 1}) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})
    (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
      (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S) :
    (stdSimplex.δ j ▷ (SSet.uliftFunctor.{u + 1, u}).obj B) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k = functorSimplexDiagram S := by
  rw [coherentColimitUnitPointedTetrahedronDiagram, functorSimplexDiagram_pre]
  have h : stdSimplex.δ j ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = S := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact hS
  rw [h]

/-- 元の全三単体の選択を、同じ始点を含む同じ全二面へ制限する射。 -/
def coherentColimitUnitPointedTetrahedronFaceRestriction (j : Fin 4) (hj : j ≠ 0) :=
  tetrahedronFaceExtensionRestriction pointedSpaceProjection
    ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k)
    (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 3 _
      (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)) j hj

/-- 選択済み全三単体の面制限の頂点は、元の持ち上げの同じ全二面を表す。 -/
lemma coherentColimitUnitPointedTetrahedronFaceRestriction_vertex (j : Fin 4) (hj : j ≠ 0) :
    ((((coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj).app (Opposite.op ⦋0⦌)
      (coherentColimitUnitPointedTetrahedronChoice_vertex B T k)).val).val) =
        functorVertex ((stdSimplex.δ j ▷ leftUnstraightening F) ≫
          coherentColimitUnitPointedTetrahedron B T k) := by
  have hi : (scaffoldFirstVertex 3 ▷ leftUnstraightening F) ≫
      coherentColimitUnitPointedTetrahedron B T k = leftUnstraighteningSimplexStart F := by
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc,
      coherentColimitUnitPointedTetrahedron_initial]
    rfl
  exact congrArg (fun z => z.val.val) (relativeExtensionRestriction_vertex pointedSpaceProjection
    ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k)
    (scaffoldFirstVertex 3 ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 3 _
      (coherentColimitUnitPointedTetrahedronDiagram_initial B T k))
    (stdSimplex.δ j ▷ leftUnstraightening F) (𝟙 _) (scaffoldFirstVertex 2 ▷ _)
    (tetrahedronFace_initial_prism _ j hj) (coherentColimitUnitPointedTetrahedron B T k)
    (coherentColimitUnitPointedTetrahedron_projection B T k) hi)

/-- 元の全空間に引き戻した二面の底も、元の指定面図式の同じ引き戻しに厳密に一致。 -/
lemma coherentColimitUnitPointedTetrahedronDiagram_face_base (j : Fin 4)
    (S : (Δ[2] : SSet.{u + 1}) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})
    (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
      (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S) :
    (stdSimplex.δ j ▷ leftUnstraightening F) ≫
        ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
          coherentColimitUnitPointedTetrahedronDiagram B T k) =
      (Δ[2] ◁ leftUnstraighteningProjection F) ≫ functorSimplexDiagram S := by
  have he : (stdSimplex.δ j ▷ leftUnstraightening F) ≫
      (Δ[3] ◁ leftUnstraighteningProjection F) =
        (Δ[2] ◁ leftUnstraighteningProjection F) ≫
          (stdSimplex.δ j ▷ (SSet.uliftFunctor.{u + 1, u}).obj B) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [← Category.assoc, he, Category.assoc,
    coherentColimitUnitPointedTetrahedronDiagram_face B T k j S hS]

end SerrePositivity.InfinityCategories.F2
