module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexMarkedColimit

/-!
概要：底の小さい余極限は、反転関手の実際の極限へ写る。
方針：周囲の関手単体集合の極限の普遍射を、全頂点で反転関手へ戻す。
規約：標的の quasicategory 性や底の図式の単射性は不要。
使われ方：小余積と骨格の極限で局所化比較を貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 任意の小さい余極限に沿う反転関手の制限は、実際の極限錐をなす。 -/
def transportSimplexInvertingConeIsLimit {J : Type v} [SmallCategory J]
    {F : J ⥤ SSet.{max u v}} {c : Cocone F} (hc : IsColimit c) (E : SSet.{max u v}) :
    IsLimit ((transportSimplexInvertingDiagram E).mapCone c.op) := by
  let H := internalHom.flip.obj E
  let a := H.mapCone (transportSimplexNerveFunctor.mapCocone c).op
  have ha : IsLimit a := isLimitOfPreserves H (transportSimplexNerveCoconeIsColimit hc).op
  let η := Functor.whiskerLeft F.op (transportSimplexInvertingInclusion E)
  let forget (s : Cone (F.op ⋙ transportSimplexInvertingDiagram E)) :=
    (Cone.postcompose η).obj s
  have hv (s : Cone (F.op ⋙ transportSimplexInvertingDiagram E)) (v : s.pt _⦋0⦌) :
      IsInvertingFunctorVertex _ E (transportSimplexInitialEdges c.pt)
        ((ha.lift (forget s)).app (Opposite.op ⦋0⦌) v) := by
    apply (isInvertingFunctorVertex_iff_of_isColimit hc _).mpr
    intro j
    have hf : ha.lift (forget s) ≫
        (pre (nerveMap (transportSimplexFunctor (c.ι.app j)))).app E =
          s.π.app (Opposite.op j) ≫
            (invertingFunctors (nerve (TransportSimplexCategory (F.obj j))) E
              (transportSimplexInitialEdges (F.obj j))).ι := ha.fac (forget s) (Opposite.op j)
    have hj := fullSubcomplexOnVertices_vertex
      ((s.π.app (Opposite.op j)).app (Opposite.op ⦋0⦌) v)
    have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) hf
    exact he.symm ▸ hj
  let L (s : Cone (F.op ⋙ transportSimplexInvertingDiagram E)) :=
    fullSubcomplexLift (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges c.pt))
      (ha.lift (forget s)) (hv s)
  have hL (s : Cone (F.op ⋙ transportSimplexInvertingDiagram E)) :
      L s ≫ (invertingFunctors (nerve (TransportSimplexCategory c.pt)) E
        (transportSimplexInitialEdges c.pt)).ι = ha.lift (forget s) := fullSubcomplexLift_ι _ _ _
  refine { lift := L, fac := ?_, uniq := ?_ }
  · intro s j
    apply (cancel_mono (invertingFunctors (nerve (TransportSimplexCategory (F.obj j.unop))) E
      (transportSimplexInitialEdges (F.obj j.unop))).ι).mp
    change (L s ≫ transportSimplexInvertingRestriction (c.ι.app j.unop) E) ≫ _ = _
    rw [Category.assoc, transportSimplexInvertingRestriction_ι, ← Category.assoc]
    change (L s ≫ (invertingFunctors (nerve (TransportSimplexCategory c.pt)) E
      (transportSimplexInitialEdges c.pt)).ι) ≫
        (pre (nerveMap (transportSimplexFunctor (c.ι.app j.unop)))).app E = _
    rw [hL]
    exact ha.fac (forget s) j
  · intro s m hm
    apply (cancel_mono (invertingFunctors (nerve (TransportSimplexCategory c.pt)) E
      (transportSimplexInitialEdges c.pt)).ι).mp
    rw [hL]
    apply ha.uniq (forget s)
    intro j
    change (m ≫ (invertingFunctors (nerve (TransportSimplexCategory c.pt)) E
      (transportSimplexInitialEdges c.pt)).ι) ≫
        (pre (nerveMap (transportSimplexFunctor (c.ι.app j.unop)))).app E =
      s.π.app j ≫ (invertingFunctors (nerve (TransportSimplexCategory (F.obj j.unop))) E
        (transportSimplexInitialEdges (F.obj j.unop))).ι
    rw [Category.assoc, ← transportSimplexInvertingRestriction_ι, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ _) (hm j)

end SerrePositivity.InfinityCategories
