module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFaceRestriction

/-!
概要：元の単位三単体の選択済み比較を、同じ始点の二面の選択済み比較へ厳密に移す。
方針：元の全延長の面制限と、同じ初期値を持つ制限先の可縮性を使う。
規約：元の比較の値を保持。使われ方：共有面の比較と指定合成則の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)
local notation "b₃" => (Δ[3] ◁ leftUnstraighteningProjection F) ≫
  coherentColimitUnitPointedTetrahedronDiagram B T k
local notation "h₃" => leftUnstraighteningSimplexStart_projection F 3
  (coherentColimitUnitPointedTetrahedronDiagram B T k)
  (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)

/-- 元の単位三単体の二面と、同じ元の pointed 初期値を固定した全選択空間。 -/
def coherentColimitUnitPointedTetrahedronFaceChoice (j : Fin 4) (hj : j ≠ 0) :=
  relativeFunctorExtensionSpace pointedSpaceProjection
    ((stdSimplex.δ j ▷ leftUnstraightening F) ≫ b₃) (scaffoldFirstVertex 2 ▷ _)
    (𝟙 _ ≫ leftUnstraighteningSimplexStart F)
    (by rw [Category.assoc, h₃, ← Category.assoc,
      ← tetrahedronFace_initial_prism _ j hj, Category.assoc])

/-- 同じ pointed 初期値を持つ元の二面の全選択空間は可縮。 -/
lemma coherentColimitUnitPointedTetrahedronFaceChoice_contractible (j : Fin 4) (hj : j ≠ 0) :
    IsContractibleKan (coherentColimitUnitPointedTetrahedronFaceChoice B T k j hj) :=
  tetrahedronFaceExtensionRestriction_contractible pointedSpaceProjection b₃
    (leftUnstraighteningSimplexStart F) h₃ j hj

/-- 任意の元の指定比較は、面へ制限すると同じ面の選択済み比較そのもの。 -/
lemma coherentColimitUnitPointedTetrahedronFaceComparison (j : Fin 4) (hj : j ≠ 0)
    {x y : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e (coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj) =
      (coherentColimitUnitPointedTetrahedronFaceChoice_contractible B T k j hj).vertexIso
        ((coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj).app _ x)
        ((coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj).app _ y) :=
  tetrahedronFaceExtensionRestriction_vertexIso pointedSpaceProjection b₃
    (leftUnstraighteningSimplexStart F) h₃ j hj e

/-- 面へ制限した二つの元の指定比較の合成は、同じ直接比較の選択済みの値に等しい。 -/
lemma coherentColimitUnitPointedTetrahedronFaceComparison_trans (j : Fin 4) (hj : j ≠ 0)
    {x y z : (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌}
    (e : VertexIso x y) (f : VertexIso y z) :
    VertexIso.map e (coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj) ≪≫
        VertexIso.map f (coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj) =
      (coherentColimitUnitPointedTetrahedronFaceChoice_contractible B T k j hj).vertexIso
        ((coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj).app _ x)
        ((coherentColimitUnitPointedTetrahedronFaceRestriction B T k j hj).app _ z) :=
  tetrahedronFaceExtensionRestriction_comparison_trans pointedSpaceProjection b₃
    (leftUnstraighteningSimplexStart F) h₃ j hj e f

end SerrePositivity.InfinityCategories.F2
