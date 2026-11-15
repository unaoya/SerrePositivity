module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementParameter

/-!
概要：元の全 pinched 族の各単体を同じ終端の実評価像へ同定する。
方針：同じ普遍評価式を恒等単体で評価し、同じ終端パラメータの式を使う。
規約：HA Construction 1.3.1.13、全列・全次数。
使われ方：元の全実屋根と同じ pinched 族の評価三角形。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementPinchedMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c =
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))))).app (op ⦋n⦌)
      (strictRawModuleTensorElementPinchedSimplex A X P Q c) := by
  have he := strictRawModuleTensorElementPinchedFamily_evaluation A X P Q c
  rw [moduleTensorHomPinchedSimplex_reindex] at he
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) Q) =>
      f.app (op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))) he
  rw [strictRawModuleTensorHomPinchedSimplex_id_eval] at h
  exact (congrArg ((strictRawModuleTensorPinchedIso A X P Q).hom.app (op ⦋n⦌))
    (strictRawModuleTensorElementParameterMap_app A X P Q c)).trans h.symm

end SerrePositivity.EInfinity.BarrattEccles
