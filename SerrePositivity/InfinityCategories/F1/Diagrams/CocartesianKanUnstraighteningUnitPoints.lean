module

public import SerrePositivity.InfinityCategories.F1.Diagrams.CocartesianKanUnstraighteningUnit
public import SerrePositivity.InfinityCategories.F1.KanModels.KanAnodyneLocalization

/-!
概要：全族単位の同じ全 fiber 回収から、元の指定点との fiber 内同型を反映する。
方針：Kan 置換後の恒等射評価の同値性を示し、同じ値回収の充満忠実性を使う。
規約：全族写像・fiber 回収同型・指定点を共に固定し、補助点を選び直さない。
使われ方：Ind-S (5)、K-B-S の既存指定恒等点との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- Kan 置換後の同じ恒等射評価は、実際の Kan 複体間の同値。 -/
lemma cocartesianKanUnitEvaluation_isQCatEquivalence
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget)
    (hη : ∀ X, SSet.anodyneExtensions (η.app X)) (c : I) :
    IsQCatEquivalence (R.map (cocartesianStrictTransportEvaluate p c)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  let e := cocartesianStrictTransportFiberEquivalence p c
  let q : Q.obj (cocartesianStrictTransport p c) ≅ Q.obj (vertexFiber p (nerveVertex c)) :=
    { hom := Q.map e.hom
      inv := Q.map e.inv
      hom_inv_id := by
        rw [← Q.map_comp]
        exact (AnodyneHomotopy.map_homotopy_eq Q hQ e.homInvIso.simplicialHomotopy).trans
          (Q.map_id _)
      inv_hom_id := by
        rw [← Q.map_comp]
        exact (AnodyneHomotopy.map_homotopy_eq Q hQ e.invHomIso.simplicialHomotopy).trans
          (Q.map_id _) }
  have : IsIso (Q.map (cocartesianStrictTransportEvaluate p c)) := q.isIso_hom
  have : IsIso (Q.map (η.app (cocartesianStrictTransport p c))) := hQ _ (hη _)
  have : IsIso (Q.map (η.app (vertexFiber p (nerveVertex c)))) := hQ _ (hη _)
  have hn := congrArg (fun k => Q.map k) (η.naturality (cocartesianStrictTransportEvaluate p c))
  simp only [Functor.map_comp] at hn
  change Q.map (cocartesianStrictTransportEvaluate p c) ≫
      Q.map (η.app (vertexFiber p (nerveVertex c))) =
    Q.map (η.app (cocartesianStrictTransport p c)) ≫
      Q.map (R.map (cocartesianStrictTransportEvaluate p c)) at hn
  have he : Q.map (R.map (cocartesianStrictTransportEvaluate p c)) =
      inv (Q.map (η.app (cocartesianStrictTransport p c))) ≫
        Q.map (cocartesianStrictTransportEvaluate p c) ≫
        Q.map (η.app (vertexFiber p (nerveVertex c))) := by
    rw [hn, IsIso.inv_hom_id_assoc]
  apply isQCatEquivalence_of_anodyneQ_isIso
  change IsIso (Q.map (R.map (cocartesianStrictTransportEvaluate p c)))
  rw [he]
  infer_instance

/-- 同じ全 fiber 回収で指定点の値を照合すれば、実際の単位像と指定点は同じ fiber 内で同型。 -/
def cocartesianKanUnstraighteningUnit_pointIso
    {I : Type u} [Category.{u} I] {E : SSet.{u}}
    (p : E ⟶ nerve I) [CocartesianFibration p]
    (R : SSet.{u} ⥤ KanObject.{u}) (η : 𝟭 SSet.{u} ⟶ R ⋙ kanObjectForget)
    (hη : ∀ X, SSet.anodyneExtensions (η.app X))
    (f : E ⟶ smallLeftUnstraightening
      (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)))
    (hf : f ≫ smallLeftUnstraighteningProjection
      (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) = p)
    (c : I)
    (e : FunctorIso
      (vertexFiberMap p _ f hf (nerveVertex c) ≫
        (smallLeftUnstraighteningFiberValueEquivalence
          (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) (nerveVertex c)).hom ≫
        R.map (cocartesianStrictTransportEvaluate p c))
      (η.app (vertexFiber p (nerveVertex c))))
    (x : (vertexFiber p (nerveVertex c)) _⦋0⦌)
    (v : (vertexFiber (smallLeftUnstraighteningProjection
      (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R))) (nerveVertex c)) _⦋0⦌)
    (hv : VertexIso
      (((smallLeftUnstraighteningFiberValueEquivalence
        (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R)) (nerveVertex c)).hom ≫
        R.map (cocartesianStrictTransportEvaluate p c)).app (Opposite.op ⦋0⦌) v)
      ((η.app (vertexFiber p (nerveVertex c))).app (Opposite.op ⦋0⦌) x)) :
    VertexIso ((vertexFiberMap p _ f hf (nerveVertex c)).app (Opposite.op ⦋0⦌) x) v := by
  have : Quasicategory (vertexFiber p (nerveVertex c)) :=
    vertexFiber_quasicategory_of_innerFibration p (nerveVertex c)
  have he := (smallLeftUnstraighteningFiberValueEquivalence
    (kanDiagramCoherentNerve (cocartesianStrictTransportDiagram p ⋙ R))
    (nerveVertex c)).isQCatEquivalence.comp (cocartesianKanUnitEvaluation_isQCatEquivalence p R η hη c)
  exact he.isFullyFaithful.preimageVertexIso ((FunctorIso.app e x) ≪≫ hv.symm)

end SerrePositivity.InfinityCategories
