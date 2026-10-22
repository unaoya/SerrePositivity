module
public import SerrePositivity.KST.Fibration.FirstVertexStrictSection
public import SerrePositivity.KST.Fibration.NativeRepresentationPoint

/-! # 同じ厳密切断の恒等射評価を、元の初頂点 fiber の同じ点として回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) (c : TransportSimplexCategory B)

/-- 初頂点の pullback fiber を、元の同じ初頂点 fiber へ第一射影で送る。 -/
def firstVertexFiberProjection :
    vertexFiber (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c) ⟶
      vertexFiber p ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)) :=
  vertexFiberLift p _ (vertexFiberι
    (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c) ≫
      pullback.fst p (transportSimplexFirstVertexMap B)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, vertexFiberι_comp, SSet.const_comp])

/-- 元の全空間へ含めると同じ第一射影そのもの。 -/
theorem firstVertexFiberProjection_ι :
    firstVertexFiberProjection p c ≫ vertexFiberι p
      ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)) =
    vertexFiberι (pullback.snd p (transportSimplexFirstVertexMap B)) (nerveVertex c) ≫
      pullback.fst p (transportSimplexFirstVertexMap B) := rfl

/-- 元の単体切断点から、同じ厳密持ち上げと恒等射評価で得る元の fiber 点。 -/
def firstVertexSectionFiberPoint
    (v : (relativeFunctorSpace p
      ((transportSimplexDomainFunctor B).obj (Opposite.op c)).hom) _⦋0⦌) :
    (vertexFiber p ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌)
      (nerveVertex c))) _⦋0⦌ :=
  (firstVertexFiberProjection p c).app (Opposite.op ⦋0⦌)
    ((leftStrictTransportEvaluate (pullback.snd p (transportSimplexFirstVertexMap B)) c).app
      (Opposite.op ⦋0⦌) ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v))

/-- この同じ fiber 点の全空間の値は、元の単体切断の初頂点そのもの。 -/
theorem firstVertexSectionFiberPoint_val
    (v : (relativeFunctorSpace p
      ((transportSimplexDomainFunctor B).obj (Opposite.op c)).hom) _⦋0⦌) :
    (firstVertexSectionFiberPoint p c v).val = v.val.app (Opposite.op ⦋0⦌) (𝟙 _)
      (stdSimplex.obj₀Equiv.symm (0 : Fin (c.objDown.obj.unop.len + 1))) :=
  firstVertexStrictSectionMap_evaluate_fst p c v

variable [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

local instance : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

/-- 同じ表現の native 制限の実点は、第一射影した同じ元の fiber 点の pointedMap 像。 -/
theorem nativeRestrict_firstVertex_point
    (w : (vertexFiber (pullback.snd p (transportSimplexFirstVertexMap B))
      (nerveVertex c)) _⦋0⦌) :
    (transportRepresentationPointedFiberMap (R.nativeRestrict (transportSimplexFirstVertexMap B))
      (ULift.up (nerveVertex c))).app (Opposite.op ⦋0⦌)
        ((uliftVertexFiberIso (pullback.snd p (transportSimplexFirstVertexMap B))
          (nerveVertex c)).hom.app (Opposite.op ⦋0⦌) (ULift.up w)) =
    (transportRepresentationPointedFiberMap R
      (ULift.up ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)))).app
        (Opposite.op ⦋0⦌) ((uliftVertexFiberIso p
          ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c))).hom.app
            (Opposite.op ⦋0⦌) (ULift.up ((firstVertexFiberProjection p c).app
              (Opposite.op ⦋0⦌) w))) := by
  apply Subtype.ext
  change (R.nativeRestrict (transportSimplexFirstVertexMap B)).pointedMap.app
      (Opposite.op ⦋0⦌) (ULift.up w.val) =
    R.pointedMap.app (Opposite.op ⦋0⦌) (ULift.up
      ((pullback.fst p (transportSimplexFirstVertexMap B)).app (Opposite.op ⦋0⦌) w.val))
  exact congrArg (fun m => m.app (Opposite.op ⦋0⦌) (ULift.up w.val))
    (R.nativeRestrict_pointedMap (transportSimplexFirstVertexMap B))

end SerrePositivity.KST.Fibration
