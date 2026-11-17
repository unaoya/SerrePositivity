module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinched
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameIndexAugmentation

/-!
概要：元の全 frame 要素列を、同じ終端パラメータと全 pinched 族へ送る。
方針：元の要素圏の同じ Hom 持ち上げ、既存の終端写像と実 Hom 同型を使う。
規約：HA Construction 1.3.1.13、全次数・全作用素。
使われ方：元の K の Hom 誘導射と全評価屋根の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorElementLiftMap : strictRawModuleTensorElementIndex A X P Q ⥤
    ULiftHom.{u + 1} (((((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q).Elements)ᵒᵖ) :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙ ULiftHom.up

def strictRawModuleTensorElementLiftNerveMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    nerve (ULiftHom.{u + 1} (((((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q).Elements)ᵒᵖ)) where
  app _ := ↾fun Γ => Γ ⋙ strictRawModuleTensorElementLiftMap A X P Q
  naturality _ _ _ := rfl

def strictRawModuleTensorElementParameterMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    SSet.uliftFunctor.{u + 1, u}.obj (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q) :=
  strictRawModuleTensorElementLiftNerveMap A X P Q ≫
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{u, u + 1}
      (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q)

def strictRawModuleTensorPinchedIso :
    SSet.uliftFunctor.{u + 1, u}.obj (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q) ≅
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) Q) :=
  SSet.uliftFunctor.{u + 1, u}.mapIso
    (((moduleTensorHomDoldKanBifunctorIso A (dgAlgebraCategory A ((assocForget A).obj X))).app
      (op ((strictRawModuleProbeFunctor A X).obj P))).app Q) ≪≫
    moduleDoldKanPinchedIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P) Q

def strictRawModuleTensorElementPinchedMap : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q) :=
  strictRawModuleTensorElementParameterMap A X P Q ≫ (strictRawModuleTensorPinchedIso A X P Q).hom

lemma strictRawModuleTensorElementParameterMap_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorElementParameterMap A X P Q).app (op ⦋n⦌) c =
      ULift.up (((strictRawModuleProbeTensorFrame A X).obj P).map
        (strictRawModuleTensorElementTerminalParameter A X P Q c) ≫
          (strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))) := rfl

lemma strictRawModuleTensorHomPinchedSimplex_id_eval (n : ℕ)
    (g : ((strictRawModuleProbeTensorFrame A X).obj P).obj ⦋n⦌ ⟶ Q) :
    (moduleTensorHomPinchedSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P) Q ⦋n⦌ g).app (op ⦋n⦌)
      (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      (strictRawModuleTensorPinchedIso A X P Q).hom.app (op ⦋n⦌) (ULift.up g) := by
  change (moduleDoldKanPinchedIso A (dgAlgebraCategory A ((assocForget A).obj X))
    ((strictRawModuleProbeFunctor A X).obj P) Q).hom.app (op ⦋n⦌)
    (ULift.up ((((moduleTensorHomDoldKanBifunctorIso A (dgAlgebraCategory A ((assocForget A).obj X))).app
      (op ((strictRawModuleProbeFunctor A X).obj P))).app Q).hom.app (op ⦋n⦌)
      (SSet.yonedaEquiv (moduleTensorHomRepresentable A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P) Q ⦋n⦌ g)))) = _
  exact congrArg (fun f : ((strictRawModuleProbeTensorFrame A X).obj P).obj ⦋n⦌ ⟶ Q =>
    (moduleDoldKanPinchedIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P) Q).hom.app (op ⦋n⦌)
      (ULift.up ((((moduleTensorHomDoldKanBifunctorIso A (dgAlgebraCategory A ((assocForget A).obj X))).app
        (op ((strictRawModuleProbeFunctor A X).obj P))).app Q).hom.app (op ⦋n⦌) f)))
    ((SSet.yonedaEquiv (X := (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q))
      (n := ⦋n⦌)).apply_symm_apply g)

end SerrePositivity.EInfinity.BarrattEccles
