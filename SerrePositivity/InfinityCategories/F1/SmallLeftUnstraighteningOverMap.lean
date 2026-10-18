module

public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.LeftFibrationFiberReflection

/-!
概要：元の unstraightening の底上の射を小さい全空間へ移す。
方針：縮小の同型で射を共役し、fiber の宇宙移送と可換であることを示す。
規約：底は元の小さい単体集合 B に固定する。
使われ方：Kerodon Corollary 5.6.0.6、coherent な図式の関手同型を小さい fibration の比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の全空間の射を小さい unstraightening の全空間の射へ移す。
方針：二つの縮小同型を使う射の移送を適用する。
規約：底上の可換性は次の補題で別に保持する。
使われ方：Kerodon Corollary 5.6.0.6、大きい構成から小さい比較射を得る。 -/
noncomputable def smallLeftUnstraighteningOverMap {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    smallLeftUnstraightening F ⟶ smallLeftUnstraightening G :=
  smallSimplicialMap f

/-- 概要：全空間の射の縮小は元の全空間との同型に関して自然。
方針：一般の縮小写像の自然性を unstraightening の同型の表示で使う。
規約：底の条件を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6、底の可換性と fiber の自然性を移す。 -/
lemma smallLeftUnstraighteningOverMap_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G) :
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningOverMap F G f) ≫
      (smallLeftUnstraighteningIso G).hom = (smallLeftUnstraighteningIso F).hom ≫ f :=
  smallSimplicialMap_naturality f

/-- 概要：元の底上の射を縮小した射も底を保つ。
方針：宇宙を持ち上げ、縮小同型の自然性と元の底の条件を計算する。
規約：h は元の射影の厳密な可換性。
使われ方：Kerodon Corollary 5.6.0.6、小さい相対関手空間に比較射を入れる条件。 -/
lemma smallLeftUnstraighteningOverMap_projection {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) :
    smallLeftUnstraighteningOverMap F G f ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection F := by
  apply (SSet.uliftFunctor.{u + 1, u}).map_injective
  rw [Functor.map_comp, ← smallLeftUnstraighteningIso_projection G,
    ← Category.assoc, smallLeftUnstraighteningOverMap_naturality, Category.assoc, h,
    smallLeftUnstraighteningIso_projection F]

/-- 概要：小さい fiber の同型を元の全空間に含めると縮小の全空間の同型を回収する。
方針：fiber の宇宙移送と全空間の同型が誘導する fiber 射の包含を計算する。
規約：底の頂点 c とその ULift を固定する。
使われ方：Kerodon Corollary 5.6.0.6、縮小した射の fiber への制限の自然性。 -/
lemma smallLeftUnstraighteningFiberIso_hom_ι {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : B _⦋0⦌) :
    (smallLeftUnstraighteningFiberIso F c).hom ≫
        vertexFiberι (leftUnstraighteningProjection F) (ULift.up c) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberι (smallLeftUnstraighteningProjection F) c) ≫
          (smallLeftUnstraighteningIso F).hom := by
  change (uliftVertexFiberIso (smallLeftUnstraighteningProjection F) c).hom ≫
    vertexFiberMap _ _ (smallLeftUnstraighteningIso F).hom
      (smallLeftUnstraighteningIso_projection F) (ULift.up c) ≫
        vertexFiberι (leftUnstraighteningProjection F) (ULift.up c) = _
  rw [vertexFiberMap_ι, ← Category.assoc, uliftVertexFiberIso_hom_ι]

/-- 概要：小さい全空間への射の移送は fiber の縮小同型と可換。
方針：元の全空間への包含後に射の自然性を使う。
規約：h は元の底上の射の可換性。
使われ方：Kerodon Corollary 5.6.0.6、大きい fiber の同値を小さい fiber へ反映する。 -/
lemma smallLeftUnstraighteningOverMap_fiber_naturality {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F) (c : B _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningOverMap F G f) (smallLeftUnstraighteningOverMap_projection F G f h) c) ≫
        (smallLeftUnstraighteningFiberIso G c).hom =
      (smallLeftUnstraighteningFiberIso F c).hom ≫
        vertexFiberMap (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
          f h (ULift.up c) := by
  apply vertexFiber_hom_ext (leftUnstraighteningProjection G) (ULift.up c)
  simp only [Category.assoc, vertexFiberMap_ι]
  rw [smallLeftUnstraighteningFiberIso_hom_ι, ← Category.assoc,
    ← Functor.map_comp, vertexFiberMap_ι, Functor.map_comp,
    Category.assoc, smallLeftUnstraighteningOverMap_naturality,
    ← Category.assoc, ← smallLeftUnstraighteningFiberIso_hom_ι, Category.assoc]

/-- 概要：大きい unstraightening の底上の前合成同値は小さい全空間の前合成同値へ移る。
方針：大きい fiber での同値を縮小同型で移し、Kan 複体の宇宙移送から反映して全空間へ戻す。
規約：底 B の quasicategory 性だけを追加で仮定する。
使われ方：Kerodon Corollary 5.6.0.6、図式の関手同型による小さい unstraightening の同値不変性。 -/
lemma smallLeftUnstraighteningOverMap_isPrecompositionEquivalence
    {B : SSet.{u}} [Quasicategory B]
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (h : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (ef : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence (smallLeftUnstraighteningOverMap F G f) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningOverMap F G f) (smallLeftUnstraighteningOverMap_projection F G f h)
  intro c
  apply (isQCatEquivalence_ulift_iff_of_kan _).mp
  apply (qCatEquivalenceOfIso (smallLeftUnstraighteningFiberIso G c)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).map
    (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningOverMap F G f) (smallLeftUnstraighteningOverMap_projection F G f h) c) ≫
        (smallLeftUnstraighteningFiberIso G c).hom)
  rw [smallLeftUnstraighteningOverMap_fiber_naturality F G f h c]
  exact (qCatEquivalenceOfIso (smallLeftUnstraighteningFiberIso F c)).isQCatEquivalence.comp
    (vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence
      (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) f h ef (ULift.up c))

end SerrePositivity.InfinityCategories
