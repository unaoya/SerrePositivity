module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementDiagram
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleDiagramSource
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantAdjunct

/-!
# 同じ全 frame 単体の指定模型における実評価屋根

概要：M10 の全単体の同じ augmentation と評価を、指定模型の同じ全関手の射へ送る。
方針：同じ全 augmentation 同型を反転し、同じ全評価円柱の射と合成する。
規約：HA §1.3.4、元の全作用素と同じ定値端点を保持する。
使われ方：同じ K の Hom 誘導射と全高次の実評価の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全 frame augmentation の像を同じ全関手同型として保持する。
方針：元の全円柱と元の各成分の擬同型性を使う。
規約：HA §1.3.4、同じ成分。使われ方：全評価屋根の弱同値側。 -/
def strictRawModuleTensorElementSourceAugmentationIso :
    FunctorIso
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P))) :=
  strictRawModuleDiagramNatTransIso A X (strictRawModuleTensorElementAugmentation A X P Q)
    (strictRawModuleTensorElementAugmentation_weak A X P Q)

/-- 概要：元の全 frame 評価を同じ全関手の射に送る。
方針：同じ自然変換円柱の射を使う。
規約：HA §1.3.4、全パラメータ。使われ方：実屋根の元の右脚。 -/
def strictRawModuleTensorElementSourceEvaluation :
    FunctorHom
      (strictRawModuleDiagramSource A X (strictRawModuleTensorElementDiagram A X P Q))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q)) :=
  strictRawModuleDiagramNatTransHom A X (strictRawModuleTensorElementEvaluation A X P Q)

/-- 概要：同じ全 frame 単体に対する指定模型内の実評価屋根。
方針：同じ全 augmentation の逆と同じ評価射を合成する。
規約：HA §1.3.4、同じ二脚。使われ方：全高次の実 Hom 比較。 -/
def strictRawModuleTensorElementSourceRoof :
    FunctorHom
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
          ((strictRawModuleProbeFunctor A X).obj P)))
      (strictRawModuleDiagramSource A X
        ((Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q)) :=
  (strictRawModuleTensorElementSourceAugmentationIso A X P Q).inv ≫
    strictRawModuleTensorElementSourceEvaluation A X P Q

/-- 概要：同じ実屋根は元の全 augmentation と評価の三角形を満たす。
方針：同じ全関手同型の順射と逆射を相殺する。
規約：HA §1.3.4、全関手の射の等式。使われ方：元の評価円柱の回収。 -/
lemma strictRawModuleTensorElementSourceRoof_triangle :
    (strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      strictRawModuleTensorElementSourceRoof A X P Q =
        strictRawModuleTensorElementSourceEvaluation A X P Q := by
  simp only [strictRawModuleTensorElementSourceRoof, Iso.hom_inv_id_assoc]

/-- 概要：同じ実屋根の両端を元の指定頂点の定値図式に戻す。
方針：同じ定値図式の全同型を前後に合成する。
規約：HA §1.3.4、元の全パラメータ。使われ方：同じ pinched Hom との全評価比較。 -/
def strictRawModuleTensorElementSourceRoofFamily :
    ConstantFunctorHom (nerve (strictRawModuleTensorElementIndex A X P Q)) (strictModuleInfinity A X)
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj
          ((strictRawModuleProbeFunctor A X).obj P))))
      ((strictRawModuleSource A X).app (op ⦋0⦌)
        (nerveVertex ((ULiftHom.up.{u, u + 1, u + 1} (C := strictRawModuleCategory A X)).obj Q))) :=
  (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q)
    ((strictRawModuleProbeFunctor A X).obj P)).inv ≫
    strictRawModuleTensorElementSourceRoof A X P Q ≫
      (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q) Q).hom

/-- 概要：同じ定値端点への移送は元の全評価三角形を保つ。
方針：同じ定値図式の同型を相殺し、同じ元の三角式を使う。
規約：HA §1.3.4、全関手の射の等式。使われ方：K の同じ評価との照合。 -/
lemma strictRawModuleTensorElementSourceRoofFamily_triangle :
    ((strictRawModuleTensorElementSourceAugmentationIso A X P Q).hom ≫
      (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P)).hom) ≫
          strictRawModuleTensorElementSourceRoofFamily A X P Q =
      strictRawModuleTensorElementSourceEvaluation A X P Q ≫
        (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q) Q).hom := by
  dsimp only [strictRawModuleTensorElementSourceRoofFamily]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫
      (strictRawModuleDiagramSourceConstantIso A X (I := strictRawModuleTensorElementIndex A X P Q) Q).hom)
      (strictRawModuleTensorElementSourceRoof_triangle A X P Q))

end SerrePositivity.EInfinity.BarrattEccles
