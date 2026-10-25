module

public import SerrePositivity.InfinityCategories.F1.Coherent.KanLeftActionInterval
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceUniversalPrismTransport
public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransportSquareVertices
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison

/-!
概要：Kan 値豊穣関手の指定点から作る、coslice 全体上の比較。
方針：普遍 coslice prism の持ち上げを、全反転 Hom 上の豊穣合成と照合する。
規約：同じ一つの全空間射の fiber を使い、点ごとの同値を貼り合わせない。
使われ方：豊穣表現可能関手の coherent な表現性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace KanCosliceComparison

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

variable {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
  [∀ x y : C, KanComplex (SimplicialCategory.sHom x y)]
  (F : EnrichedFunctor SSet.{u} C KanObject.{u})

lemma value (y : C) :
    (coherentNerveMap F).app (Opposite.op ⦋0⦌) (coherentNerveVertex y) =
      spaceInfinityVertex (F.obj y) :=
  (coherentNerveMap_vertex F y).trans (spaceInfinityVertex_eq_coherent (F.obj y)).symm

def fiberIso (y : C) :
    vertexFiber (leftUnstraighteningProjection (coherentNerveMap F)) (coherentNerveVertex y) ≅
      vertexFiber pointedSpaceProjection (spaceInfinityVertex (F.obj y)) :=
  leftUnstraighteningFiberIso (coherentNerveMap F) (coherentNerveVertex y) ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection) (value F y))

lemma fiberIso_ι (y : C) :
    (fiberIso F y).hom ≫ vertexFiberι pointedSpaceProjection (spaceInfinityVertex (F.obj y)) =
    vertexFiberι (leftUnstraighteningProjection (coherentNerveMap F)) (coherentNerveVertex y) ≫
      pullback.fst pointedSpaceProjection (coherentNerveMap F) := by
  dsimp only [fiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection (value F y)]
  exact leftUnstraighteningFiberIso_hom_ι _ _

lemma fiberIso_square (y : C) :
    transportSquareFiberMap (leftUnstraighteningProjection (coherentNerveMap F))
      pointedSpaceProjection (pullback.fst pointedSpaceProjection (coherentNerveMap F))
      (coherentNerveMap F) pullback.condition (coherentNerveVertex y) ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) (value F y)) = (fiberIso F y).hom := by
  apply (cancel_mono (vertexFiberι pointedSpaceProjection (spaceInfinityVertex (F.obj y)))).1
  rw [Category.assoc, vertexFiberTransport_ι pointedSpaceProjection (value F y)]
  erw [transportSquareFiberMap_ι]
  exact (fiberIso_ι F y).symm

variable (x : C)
  (c : (((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject
    (F.obj x))).op) _⦋0⦌)

def pointed : (vertexFiber pointedSpaceProjection (spaceInfinityVertex (F.obj x))) _⦋0⦌ :=
  (pointedReverseKanFiberComparison (F.obj x)).app (Opposite.op ⦋0⦌) c

def start :
    (vertexFiber (leftUnstraighteningProjection (coherentNerveMap F))
      (coherentNerveVertex x)) _⦋0⦌ :=
  (fiberIso F x).inv.app (Opposite.op ⦋0⦌) (pointed F x c)

lemma start_pointed :
    (fiberIso F x).hom.app (Opposite.op ⦋0⦌) (start F x c) = pointed F x c := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (fiberIso F x).inv_hom_id (Opposite.op ⦋0⦌)) (pointed F x c)

lemma start_projection :
    (leftUnstraighteningProjection (coherentNerveMap F)).app (Opposite.op ⦋0⦌)
      (start F x c).val = coherentNerveVertex x := by
  simpa only [PinchedHom.constant_zero] using (start F x c).property

/-- 同じ指定点を恒等錐で回収する、底を保つ一つの全空間射。 -/
def map : sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) ⟶
    leftUnstraightening (coherentNerveMap F) :=
  cosliceUniversalPrismLiftEndpoint (leftUnstraighteningProjection (coherentNerveMap F))
    (coherentNerveVertex x) (start F x c).val (start_projection F x c)

lemma projection : map F x c ≫ leftUnstraighteningProjection (coherentNerveMap F) =
    sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) :=
  cosliceUniversalPrismLiftEndpoint_projection _ _ _ _

lemma identity : (map F x c).app (Opposite.op ⦋0⦌)
    (cosliceIdentityCone (coherentNerveVertex x)) = (start F x c).val :=
  cosliceUniversalPrismLiftEndpoint_identity _ _ _ _

def fiberMap (y : C) :
    vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
      (coherentNerveVertex y) ⟶
    vertexFiber pointedSpaceProjection (spaceInfinityVertex (F.obj y)) :=
  vertexFiberMap _ _ (map F x c) (projection F x c) (coherentNerveVertex y) ≫ (fiberIso F y).hom

def action (y : C) :
    ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom x y)).op ⟶
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject (F.obj y))).op :=
  lift (SSet.const c) (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (F.map x y))) ≫
    coherentReverseHomComposition (Opposite.op (F.obj y)) (Opposite.op (F.obj x))
      (Opposite.op pointKanObject)

def fiber_transportIso (y : C) :
    FunctorIso (fiberMap F x c y)
      (diagonalFiberTransport pointedSpaceProjection (SSet.const (pointed F x c))
        (cosliceFiberToIntervalMappingSpace (coherentNerveVertex x) (coherentNerveVertex y) ≫
          intervalMappingPostOfEq (coherentNerveMap F) (coherentNerveVertex x)
            (coherentNerveVertex y) (value F x) (value F y))) := by
  have e₀ := FunctorIso.postcomp
    (cosliceUniversalPrismLiftEndpoint_transportIso
      (leftUnstraighteningProjection (coherentNerveMap F))
      (coherentNerveVertex x) (start F x c).val (start_projection F x c) (coherentNerveVertex y))
    (fiberIso F y).hom
  have e₁ := diagonalFiberTransport_squareOfEqIso
    (leftUnstraighteningProjection (coherentNerveMap F)) pointedSpaceProjection
    (pullback.fst pointedSpaceProjection (coherentNerveMap F)) (coherentNerveMap F)
    pullback.condition (value F x) (value F y) (SSet.const (start F x c))
    (cosliceFiberToIntervalMappingSpace (coherentNerveVertex x) (coherentNerveVertex y))
  rw [fiberIso_square, fiberIso_square, SSet.const_comp, start_pointed] at e₁
  exact e₀ ≪≫ e₁

/-- 全反転 Hom 上で、実際の大域射の fiber は指定係数への豊穣作用そのもの。 -/
def fiber_actionIso (y : C) :
    FunctorIso
      (((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom x y)).inv ≫
        HomotopyLimits.coherentCosliceFiberComparison x y) ≫ fiberMap F x c y)
      (action F x c y ≫ pointedReverseKanFiberComparison (F.obj y)) := by
  let k := (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom x y)).inv ≫
    HomotopyLimits.coherentCosliceFiberComparison x y
  have e := FunctorIso.precomp (fiber_transportIso F x c y) k
  have precomp_transport {P Q E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
      {a b : B _⦋0⦌} (s : P ⟶ vertexFiber p a) (d : P ⟶ intervalMappingSpace a b)
      (j : Q ⟶ P) :
      j ≫ diagonalFiberTransport p s d = diagonalFiberTransport p (j ≫ s) (j ≫ d) := by
    simp only [diagonalFiberTransport, ← Category.assoc, comp_lift]
  rw [precomp_transport, SSet.comp_const] at e
  have hn := coherentKanLeftHomIntervalMap_naturality F x y
  change k ≫ (cosliceFiberToIntervalMappingSpace (coherentNerveVertex x) (coherentNerveVertex y) ≫
    intervalMappingPostOfEq (coherentNerveMap F) (coherentNerveVertex x) (coherentNerveVertex y)
      (value F x) (value F y)) = _ at hn
  rw [hn] at e
  have a := pointedReverseKanCompositionTransport_diagonalIso (F.obj x) (F.obj y)
    (SSet.const c) (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (F.map x y)))
  rw [SSet.const_comp] at a
  exact e ≪≫ a.symm

/-- 合成作用の同値性から、同じ全空間射の同値性を回収する。 -/
lemma isQCatEquivalence (h : ∀ y : C, IsQCatEquivalence (action F x c y)) :
    IsQCatEquivalence (map F x c) := by
  apply isQCatEquivalence_of_leftFibration_fibers
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (leftUnstraighteningProjection (coherentNerveMap F)) (map F x c) (projection F x c)
  intro t
  obtain ⟨y, rfl⟩ := (coherentNerveVertexEquiv C).surjective t
  have ha := (h y).comp (pointedReverseKanFiberComparison_isQCatEquivalence (F.obj y))
  have hk := (qCatEquivalenceOfIso
    (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom x y)).symm).isQCatEquivalence.comp
      (HomotopyLimits.coherentCosliceFiberComparison_homotopyEquivalence x y).isQCatEquivalence
  have hf := hk.cancel_left (ha.ofFunctorIso (fiber_actionIso F x c y).symm)
  exact (qCatEquivalenceOfIso (fiberIso F y)).isQCatEquivalence.cancel_right hf

end KanCosliceComparison
end SerrePositivity.InfinityCategories
