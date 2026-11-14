module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictModules
public import SerrePositivity.EInfinity.Modules.DGResolutionAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexDerivedQuasiIsomorphisms

/-!
# BE 加群の出力解像度と同じ台の評価の比較

概要：HA §4.2.1 の忘却を、指定解像度と同じ唯一点の評価で比較する。
方針：台の評価は加群の準同型を保つので、二段の解像度を一段に比較する。
規約：基礎環上の平坦性を仮定しない。使われ方：正則加群の台の指定比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
local notation "N" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
variable (A : Type u) [CommRing A]

/-- 概要：定数一点加群の閉射を評価すると同じ複体射に戻る（HA §1.3.1）。
方針：既存の閉射表示と評価の比較を適用する。
規約：同じ鎖写像。使われ方：台の評価による準同型保存。 -/
lemma constant_evaluation_closed {P Q : Complex A}
    (f : ForgetEnrichment.of (Complex A) P ⟶ ForgetEnrichment.of (Complex A) Q) :
    (moduleEvaluation A PUnit.{1} PUnit.unit).map ((ringConstantDG A).onClosed.map f) =
      (closedToComplex A).map f := by
  have h := complexClosedPresentation_ring_evaluation A ((closedToComplex A).map f)
  have hf : (complexClosedPresentation A).map ((closedToComplex A).map f) = f :=
    (complexClosedHomEquiv A P Q).symm_apply_apply f
  rw [hf] at h
  exact h

/-- 概要：指定解像度の後の台は、同じ唯一点の実評価と全関手同型（HA §4.2.1）。
方針：評価の準同型保存で二段の出力解像度を一段にし、前合成比較を使う。
規約：同じ D(A)・同じ一点比較。使われ方：正則加群の台の指定比較。 -/
def strictModuleResolvedUnderlyingIso (X : (operad A).Algebra) :
    FunctorIso
      (moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) ≫ strictModuleUnderlying A X)
      (N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
        (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (semifreePointEquivalence A).hom) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  let V := moduleEvaluationDG A D (Opposite.op DGAlgebraPoint.star)
  let H := V.comp (ringConstantDG A)
  have e := dgModuleResolvedInfinity_compositionIso A (RightModule A D) D PUnit.{1}
    (DGFunctor.id (RightModule A D)) H (fun T => by
      rw [moduleQuasiIso_iff]
      rintro ⟨⟩
      change QuasiIso ((moduleEvaluation A PUnit.{1} PUnit.unit).map
        ((ringConstantDG A).onClosed.map (V.onClosed.map T.augmentation)))
      rw [constant_evaluation_closed]
      exact T.quasiIso (Opposite.op DGAlgebraPoint.star))
  have hid : (DGFunctor.id (RightModule A D)).comp H = H := by
    apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [hid] at e
  have p := dgModuleResolvedInfinity_precompIso A (RightModule A D) (Complex A)
    PUnit.{1} V (ringConstantDG A)
  exact FunctorIso.postcomp (e ≪≫ p) (semifreePointEquivalence A).hom

/-- 概要：正則加群の台は同じ BE carrier の D(A) 内の像（HA §4.2.1）。
方針：台の全関手比較を元の表現可能加群で評価する。
規約：同じ正則加群・同じ carrier。使われ方：相対テンソルの単位の照合。 -/
def strictModuleUnitUnderlyingIso (X : (operad A).Algebra) :
    VertexIso ((strictModuleUnderlying A X).app (Opposite.op ⦋0⦌) (strictModuleUnit A X))
      ((complexDerivedEvaluation A).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ X.carrier)) := by
  let M := representable A (Opposite.op (DGAlgebraPoint.star (R := A)
    (B := (assocForget A).obj X)))
  have e := (strictModuleResolvedUnderlyingIso A X).toNatIso.app
    (HomotopyCategory.mk (Simplex.vertex M))
  have hv := dgFunctorNerve_vertex
    (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
      (Opposite.op DGAlgebraPoint.star)) M
  change VertexIso (X := derivedInfinityCategory A)
    ((moduleResolution A (dgAlgebraCategory A ((assocForget A).obj X)) ≫ strictModuleUnderlying A X).app
      (Opposite.op ⦋0⦌) (Simplex.vertex M))
    ((N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
      (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (semifreePointEquivalence A).hom).app (Opposite.op ⦋0⦌) (Simplex.vertex M)) at e
  change VertexIso ((strictModuleUnderlying A X).app (Opposite.op ⦋0⦌) (strictModuleUnit A X)) _ at e
  rw [show (N (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
      (Opposite.op DGAlgebraPoint.star)) ≫
        dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
          (semifreePointEquivalence A).hom).app (Opposite.op ⦋0⦌) (Simplex.vertex M) =
      (dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
        (semifreePointEquivalence A).hom).app (Opposite.op ⦋0⦌)
          (Simplex.vertex X.carrier) by
    change _ = _
    rw [NatTrans.comp_app, types_comp_apply, hv]
    rfl] at e
  have hc : (nerveMap (complexClosedPresentation A) ≫ closedNerveInclusion A (Complex A)).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X.carrier) = Simplex.vertex X.carrier := by
    apply (Simplex.vertexEquiv (A := A) (D := Complex A)).injective
    rfl
  change VertexIso _ ((dgModuleResolvedInfinity A (Complex A) PUnit.{1} (ringConstantDG A) ≫
    (semifreePointEquivalence A).hom).app (Opposite.op ⦋0⦌)
      ((nerveMap (complexClosedPresentation A) ≫ closedNerveInclusion A (Complex A)).app
        (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X.carrier)))
  rw [hc]
  exact e

end SerrePositivity.EInfinity.BarrattEccles
