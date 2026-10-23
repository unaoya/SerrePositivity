module
public import SerrePositivity.KST.Fibration.FirstVertexRestrictionChart
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorActionEvaluation

/-! # 元の単体切断を under に制限して、同じ厳密な pullback strict 切断へ持ち上げる -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) (c : TransportSimplexCategory B)

/-- 元の under 制限と元の厳密底変換逆射から作る、同じ pullback strict 切断の射。 -/
def firstVertexStrictSectionMap :
    relativeFunctorSpace p ((transportSimplexDomainFunctor B).obj (Opposite.op c)).hom ⟶
      leftStrictTransport (pullback.snd p (transportSimplexFirstVertexMap B)) c :=
  relativeFunctorOverPre p
    ((transportSimplexUnderDomainTransformation B).app (Opposite.op c)) ≫
      relativeFunctorBaseChangeBackward p (transportSimplexFirstVertexMap B)
        ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom

/-- 第一射影で元の底へ戻すと、同じ元の under 制限を厳密に回収する。 -/
theorem firstVertexStrictSectionMap_forward :
    firstVertexStrictSectionMap p c ≫
      relativeFunctorBaseChangeForward p (transportSimplexFirstVertexMap B)
        ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom =
    relativeFunctorOverPre p
      ((transportSimplexUnderDomainTransformation B).app (Opposite.op c)) := by
  rw [firstVertexStrictSectionMap, Category.assoc]
  change _ ≫ (relativeFunctorBaseChangeIso p (transportSimplexFirstVertexMap B)
    ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom).inv ≫
      (relativeFunctorBaseChangeIso p (transportSimplexFirstVertexMap B)
        ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]

/-- 元の strict transport の恒等射評価は、同じ元の相対関手の実頂点評価。 -/
theorem leftStrictTransportEvaluate_vertex_val {I : Type u} [Category.{u} I]
    {F : SSet.{u}} (q : F ⟶ nerve I) (i : I) (v : (leftStrictTransport q i) _⦋0⦌) :
    ((leftStrictTransportEvaluate q i).app (Opposite.op ⦋0⦌) v).val =
      v.val.app (Opposite.op ⦋0⦌) (𝟙 _) (strictTransportUnderIdentityVertex i) := by
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (leftStrictTransportEvaluate_ι q i)
  change ((leftStrictTransportEvaluate q i).app (Opposite.op ⦋0⦌) v).val =
    v.val.app (Opposite.op ⦋0⦌) (𝟙 _)
      (PinchedHom.constant (strictTransportUnderIdentityVertex i) 0) at h
  exact h.trans (congrArg (fun z : (nerve (Under i)) _⦋0⦌ =>
    v.val.app (Opposite.op ⦋0⦌) (𝟙 _) z)
    (pinchedConstant_zero (strictTransportUnderIdentityVertex i)))

/-- 同じ持ち上げ切断の恒等射評価を第一射影で読むと、元の単体切断の初頂点を回収する。 -/
theorem firstVertexStrictSectionMap_evaluate_fst
    (v : (relativeFunctorSpace p
      ((transportSimplexDomainFunctor B).obj (Opposite.op c)).hom) _⦋0⦌) :
    (pullback.fst p (transportSimplexFirstVertexMap B)).app (Opposite.op ⦋0⦌)
      (((leftStrictTransportEvaluate
        (pullback.snd p (transportSimplexFirstVertexMap B)) c).app (Opposite.op ⦋0⦌)
          ((firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v)).val) =
      v.val.app (Opposite.op ⦋0⦌) (𝟙 _)
        (stdSimplex.obj₀Equiv.symm (0 : Fin (c.objDown.obj.unop.len + 1))) := by
  let k := transportSimplexFirstVertexMap B
  let a := ((strictTransportDomains (TransportSimplexCategory B)).obj (Opposite.op c)).hom
  let r := (firstVertexStrictSectionMap p c).app (Opposite.op ⦋0⦌) v
  let z := strictTransportUnderIdentityVertex c
  have hf := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (firstVertexStrictSectionMap_forward p c)
  have he := relativeFunctorBaseChangeForward_apply p k a r (𝟙 _) z
  have hr := relativeFunctorOverPre_apply p
    ((transportSimplexUnderDomainTransformation B).app (Opposite.op c)) v (𝟙 _) z
  have hfun := congrArg (fun t : (relativeFunctorSpace p (a ≫ k)) _⦋0⦌ =>
    t.val.app (Opposite.op ⦋0⦌) (𝟙 _) z) hf
  have h := he.symm.trans (hfun.trans hr)
  change _ = v.val.app (Opposite.op ⦋0⦌) (𝟙 _)
    ((transportSimplexUnderDomainMap c).app (Opposite.op ⦋0⦌) z) at h
  have hi := congrArg (fun z' :
      ((transportSimplexDomainFunctor B).obj (Opposite.op c)).left _⦋0⦌ =>
        v.val.app (Opposite.op ⦋0⦌) (𝟙 _) z') (transportSimplexUnderDomainMap_initial c)
  have hv := congrArg ((pullback.fst p k).app (Opposite.op ⦋0⦌))
    (leftStrictTransportEvaluate_vertex_val (pullback.snd p k) c r)
  exact hv.trans (h.trans hi)

/-- 元の初頂点制限の指定成分は、同じ厳密切断射の元の点での像を回収する。 -/
theorem firstVertexRestrictionChart_pointHom_strictSection (X : LeftFibrationObject B)
    (c : TransportSimplexCategory B)
    (v : (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X).obj
      _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      (((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).obj c).obj X)).symm v) ≫
      (straighteningFirstVertexSectionChart X c).inv ≫
        (firstVertexRestrictionChart X c).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((((relativeSectionEnrichedDiagram (strictTransportDomains
        (TransportSimplexCategory B))).precompose
          (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))).obj c).obj X)).symm
            ((firstVertexStrictSectionMap X.val.hom c).app (Opposite.op ⦋0⦌) v)) := by
  exact firstVertexRestrictionChart_pointHom X c v

end SerrePositivity.KST.Fibration
