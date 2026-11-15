module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementUniversal
public import SerrePositivity.EInfinity.Modules.TensorHomPinched

/-!
# 全要素列の同じ普遍 pinched Hom 族

概要：M10 の元の全単体列を同じ通常 dg 加群の普遍 pinched Hom 族へ送る。
方針：同じ終端パラメータと実テンソル恒等射の全族を使う。
規約：HA 1.3.1.13、全標的・終端を変える全再添字を保持する。
使われ方：元の全係数 cone の高次線形成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の全単体列の同じ終端係数を持つ普遍 pinched 族。
方針：元の終端パラメータで同じ普遍族を前合成する。
規約：HA 1.3.1.13、元の全係数。使われ方：同じ全 cone の成分。 -/
def strictRawModuleTensorElementPinchedFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A)
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) :=
  SSet.uliftFunctor.{u + 1, u}.map
    (SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫
      moduleTensorUniversalPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))

/-- 概要：同じ全 pinched 族の評価は同じ元の実評価射の族。
方針：同じ普遍評価式を同じ終端パラメータで前合成する。
規約：HA 1.3.1.13、同じ全評価。使われ方：全評価屋根の比較。 -/
lemma strictRawModuleTensorElementPinchedFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.uliftFunctor.{u + 1, u}.map
      (SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫
      moduleTensorHomPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) := by
  dsimp only [strictRawModuleTensorElementPinchedFamily]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map
      (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫ f)
      (moduleTensorUniversalPinchedSimplex_evaluation A
        (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))))

/-- 概要：同じ全 pinched 族は終端を変える全作用素と整合する。
方針：元の終端パラメータ再添字式と同じ全普遍族の自然性を合成する。
規約：HA 1.3.1.13、全ての面・退化。使われ方：全高次成分の貼り合わせ。 -/
lemma strictRawModuleTensorElementPinchedFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map θ) ≫
      strictRawModuleTensorElementPinchedFamily A X P Q c =
    strictRawModuleTensorElementPinchedFamily A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
    pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))))) := by
  dsimp only [strictRawModuleTensorElementPinchedFamily]
  rw [← Category.assoc, ← SSet.uliftFunctor.map_comp, ← SSet.stdSimplex.map_comp]
  have h := SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SimplexTerminalParameter.reindex
    (c ⋙ strictRawModuleTensorElementDegree A X P Q) θ
  change θ ≫ strictRawModuleTensorElementTerminalParameter A X P Q c =
    strictRawModuleTensorElementTerminalParameter A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (strictRawModuleTensorElementDegree A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) at h
  rw [h, SSet.stdSimplex.map_comp, SSet.uliftFunctor.map_comp, Category.assoc,
    moduleTensorUniversalPinchedSimplex_naturality]
  rfl

/-- 概要：同じ全 pinched 族を同じ恒等単体で評価する。
方針：元の全族の n 単体像を取る。
規約：HA 1.3.1.13、同じ実単体。使われ方：全 cone の線形成分。 -/
def strictRawModuleTensorElementPinchedSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))) _⦋n⦌ :=
  (strictRawModuleTensorElementPinchedFamily A X P Q c).app (op ⦋n⦌)
    (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))

/-- 概要：同じ実単体は全再添字で元の終端射の像へ移る。
方針：同じ全族の再添字式を同じ恒等単体で評価する。
規約：HA 1.3.1.13、同じ全高次。使われ方：線形再添字の実式。 -/
lemma strictRawModuleTensorElementPinchedSimplex_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A)
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))))).map θ.op
      (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDiagram A X P Q).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))))).app (op ⦋m⦌)
      (strictRawModuleTensorElementPinchedSimplex A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) := by
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[m] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A)
          ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n)))) =>
      f.app (op ⦋m⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋m⦌))))
    (strictRawModuleTensorElementPinchedFamily_reindex A X P Q c θ)
  let q : (SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u})).obj (op ⦋n⦌) :=
    ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))
  have hn := ConcreteCategory.congr_hom
    ((strictRawModuleTensorElementPinchedFamily A X P Q c).naturality θ.op) q
  exact hn.symm.trans h

end SerrePositivity.EInfinity.BarrattEccles
