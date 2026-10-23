module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTetrahedronInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorSimplexPointedStart
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TetrahedronFaceExtension

/-!
概要：元の三つの単位三単体を、元の全空間と元の pointed 始点を保って持ち上げる。
方針：同じ全三単体の始点式へ F1 の高次の持ち上げを適用し、可縮な選択空間へ束ねる。
規約：底と全初期値を保持。使われ方：指定面比較の三関係を共通の空間で読む。
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

/-- 元の単位三単体の全底上の展開。 -/
def coherentColimitUnitPointedTetrahedronDiagram :
    (Δ[3] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u} :=
  functorSimplexDiagram (SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k))

/-- 元の全底上の三単体の最初の値は、元の始域図式 F そのもの。 -/
lemma coherentColimitUnitPointedTetrahedronDiagram_initial :
    simplexPrismVertex 3 0 ((SSet.uliftFunctor.{u + 1, u}).obj B) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k = F :=
  functorSimplexDiagram_initial F _ (coherentColimitUnitTriangleTetrahedron_initial B T k)

/-- 元の全三単体と元の始点を保持した pointed な持ち上げ。 -/
def coherentColimitUnitPointedTetrahedron :
    (Δ[3] : SSet.{u + 1}) ⊗ leftUnstraightening F ⟶ PointedSpaceInfinity.{u} :=
  (exists_leftUnstraighteningSimplexLift F 3
    (coherentColimitUnitPointedTetrahedronDiagram B T k)
    (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)).choose

/-- 持ち上げの底は、元の同じ全三単体を元の全空間の射影で引き戻したもの。 -/
lemma coherentColimitUnitPointedTetrahedron_projection :
    coherentColimitUnitPointedTetrahedron B T k ≫ pointedSpaceProjection =
      (Δ[3] ◁ leftUnstraighteningProjection F) ≫
        coherentColimitUnitPointedTetrahedronDiagram B T k :=
  (exists_leftUnstraighteningSimplexLift F 3
    (coherentColimitUnitPointedTetrahedronDiagram B T k)
    (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)).choose_spec.1

/-- 元の全空間上の pointed 始点は、全時刻を通して初期面で厳密に保持される。 -/
lemma coherentColimitUnitPointedTetrahedron_initial :
    simplexPrismVertex 3 0 (leftUnstraightening F) ≫
      coherentColimitUnitPointedTetrahedron B T k = pullback.fst pointedSpaceProjection F :=
  (exists_leftUnstraighteningSimplexLift F 3
    (coherentColimitUnitPointedTetrahedronDiagram B T k)
    (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)).choose_spec.2

/-- 三単体全体と元の pointed 始点を固定する全選択空間。 -/
def coherentColimitUnitPointedTetrahedronChoice :=
  leftUnstraighteningSimplexChoiceSpace F 3
    (coherentColimitUnitPointedTetrahedronDiagram B T k)
    (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)

/-- 同じ全三単体の初期値固定の選択空間は、全高次を含めて可縮。 -/
lemma coherentColimitUnitPointedTetrahedronChoice_contractible :
    IsContractibleKan (coherentColimitUnitPointedTetrahedronChoice B T k) :=
  leftUnstraighteningSimplexChoiceSpace_isContractibleKan F 3
    (coherentColimitUnitPointedTetrahedronDiagram B T k)
    (coherentColimitUnitPointedTetrahedronDiagram_initial B T k)

/-- 選んだ元の全三単体の持ち上げを、同じ初期値固定の選択空間の実際の頂点にする。 -/
def coherentColimitUnitPointedTetrahedronChoice_vertex :
    (coherentColimitUnitPointedTetrahedronChoice B T k) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection
    ((Δ[3] ◁ leftUnstraighteningProjection F) ≫
      coherentColimitUnitPointedTetrahedronDiagram B T k)
    (scaffoldFirstVertex 3 ▷ leftUnstraightening F) (leftUnstraighteningSimplexStart F)
    (leftUnstraighteningSimplexStart_projection F 3 _
      (coherentColimitUnitPointedTetrahedronDiagram_initial B T k))
    ⟨coherentColimitUnitPointedTetrahedron B T k,
      coherentColimitUnitPointedTetrahedron_projection B T k, by
        rw [scaffoldFirstVertex_whiskerRight, Category.assoc,
          coherentColimitUnitPointedTetrahedron_initial]
        rfl⟩

end SerrePositivity.InfinityCategories.F2
