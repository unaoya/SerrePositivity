module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementDiagram
public import SerrePositivity.EInfinity.Modules.TensorHomUniversal
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.SimplexTerminalParameter

/-!
# 全 frame 単体列の元の dg Hom における普遍評価族

概要：M10 の全要素列を、同じ終端係数を持つ元の普遍 Hom 族へ送る。
方針：全終端パラメータで同じ実テンソル恒等射の族を前合成する。
規約：HA 1.3.1.13、終端を変える全ての面・退化を含む。
使われ方：元の dg 係数の全 cone と同じ実評価屋根の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全単体列を元の終端係数単体へ送る。
方針：既存の全終端パラメータを同じ次数列に適用する。
規約：HA 1.3.1.13、同じ終端対象。使われ方：全普遍 Hom 族の添字。 -/
abbrev strictRawModuleTensorElementTerminalParameter {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ⦋n⦌ ⟶ (strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)) :=
  SimplexTerminalParameter.parameter (c ⋙ strictRawModuleTensorElementDegree A X P Q)

/-- 概要：元の全単体列の同じ終端対象への実普遍 dg Hom 族。
方針：同じ恒等射の全族を同じ終端パラメータで前合成する。
規約：HA 1.3.1.13、元の主 Hom end。使われ方：全係数 cone の普遍成分。 -/
def strictRawModuleTensorElementUniversalFamily {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    SSet.stdSimplex.obj ⦋n⦌ ⟶
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).obj
        ((strictRawModuleTensorElementDiagram A X P Q).obj (c.obj (Fin.last n))) :=
  SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
    moduleTensorUniversalDoldKanSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))

/-- 概要：元の全普遍族の評価は同じ終端の実評価射の全族。
方針：同じ普遍評価式を元の終端パラメータで前合成する。
規約：HA 1.3.1.13、同じ実評価。使われ方：全高次評価三角形。 -/
lemma strictRawModuleTensorElementUniversalFamily_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementUniversalFamily A X P Q c ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) =
    SSet.stdSimplex.map (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
      moduleTensorHomDoldKanSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) := by
  dsimp only [strictRawModuleTensorElementUniversalFamily]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => SSet.stdSimplex.map
      (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫ f)
      (moduleTensorUniversalDoldKanSimplex_evaluation A
        (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))
        ((strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n)))))

/-- 概要：同じ全普遍族は終端を変える全作用素と整合する。
方針：同じ終端パラメータの再添字式と普遍族の全自然性を合成する。
規約：HA 1.3.1.13、全ての面・退化。使われ方：全係数 cone の貼り合わせ。 -/
lemma strictRawModuleTensorElementUniversalFamily_reindex {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.stdSimplex.map θ ≫ strictRawModuleTensorElementUniversalFamily A X P Q c =
      strictRawModuleTensorElementUniversalFamily A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      ((strictRawModuleProbeDoldKanHom A X).obj (op P)).map
        ((strictRawModuleTensorElementDiagram A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))) := by
  dsimp only [strictRawModuleTensorElementUniversalFamily]
  rw [← Category.assoc, ← SSet.stdSimplex.map_comp]
  have h := SimplexTerminalParameter.reindex
    (c ⋙ strictRawModuleTensorElementDegree A X P Q) θ
  change θ ≫ strictRawModuleTensorElementTerminalParameter A X P Q c =
    strictRawModuleTensorElementTerminalParameter A X P Q
      ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
        (strictRawModuleTensorElementDegree A X P Q).map
          (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) at h
  rw [h, SSet.stdSimplex.map_comp, Category.assoc, moduleTensorUniversalDoldKanSimplex_naturality]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
