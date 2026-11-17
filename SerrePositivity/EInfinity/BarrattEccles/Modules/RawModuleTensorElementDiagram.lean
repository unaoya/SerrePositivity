module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleProbeSourceTriangle
public import Mathlib.CategoryTheory.Elements

/-!
# 同じ加群 frame Hom の全単体の評価図式

概要：M10 の同じ全 Hom の全単体と全作用素を、元の augmentation と評価の図式へ束ねる。
方針：反対要素圏の次数射影を同じテンソル frame に前合成する。
規約：HA §1.3.4、元の通常局所化源と同じ宇宙表示を保持する。
使われ方：同じ K の誘導射と全高次の実評価円柱の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite _root_.HomotopicalAlgebra
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全 Hom の反対要素圏を元の局所化源の宇宙へ置く。
方針：元の要素圏に同じ二つの ULift を適用する。
規約：HA §1.3.4、全単体・全作用素。使われ方：実評価円柱の全パラメータ。 -/
abbrev strictRawModuleTensorElementIndex : Type (u + 1) :=
  ULiftHom.{u + 1} (ULift.{u + 1}
    (((((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q).Elements)ᵒᵖ))

/-- 概要：同じ全パラメータは元の局所化源と同じ Hom 宇宙の圏。
方針：既存の二つの ULift の圏構造を継承する。
規約：HA §1.3.4、同じ射。使われ方：全通常 nerve。 -/
instance strictRawModuleTensorElementIndexCategory :
    Category.{u + 1} (strictRawModuleTensorElementIndex A X P Q) := inferInstance

/-- 概要：同じ全単体のパラメータを元の単体次数へ送る。
方針：元の要素圏の射影を宇宙表示の down と合成する。
規約：HA §1.3.4、全作用素。使われ方：同じ実 frame 図式。 -/
def strictRawModuleTensorElementDegree :
    strictRawModuleTensorElementIndex A X P Q ⥤ SimplexCategory :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙
    (Functor.Elements.π (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q)).leftOp

/-- 概要：同じ全単体に対応する元のテンソル加群の図式。
方針：同じ次数射影の後に元の frame を合成する。
規約：HA §1.3.4、同じ加群。使われ方：全評価屋根の実始域。 -/
def strictRawModuleTensorElementDiagram :
    strictRawModuleTensorElementIndex A X P Q ⥤ strictRawModuleCategory A X :=
  strictRawModuleTensorElementDegree A X P Q ⋙ (strictRawModuleProbeTensorFrame A X).obj P

/-- 概要：同じ全評価図式から元の probe への全自然 augmentation。
方針：同じ frame augmentation を次数射影で前合成する。
規約：HA §1.3.4、元の射。使われ方：評価屋根の弱同値側。 -/
def strictRawModuleTensorElementAugmentation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj
        ((strictRawModuleProbeFunctor A X).obj P) :=
  Functor.whiskerLeft (strictRawModuleTensorElementDegree A X P Q)
    ((strictRawModuleProbeTensorAugmentation A X).app P)

/-- 概要：同じ全評価図式から任意の元の標的への全自然評価。
方針：元の全 Hom の単体自身を評価射にする。
規約：HA §1.3.4、全作用素の自然性。使われ方：評価屋根の元の右脚。 -/
def strictRawModuleTensorElementEvaluation :
    strictRawModuleTensorElementDiagram A X P Q ⟶
      (Functor.const (strictRawModuleTensorElementIndex A X P Q)).obj Q where
  app s := (ULiftHom.objDown s).down.unop.val
  naturality s t f := by
    change ((strictRawModuleProbeTensorFrame A X).obj P).map
        (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop ≫
      (ULiftHom.objDown t).down.unop.val = (ULiftHom.objDown s).down.unop.val ≫ 𝟙 Q
    exact (ULift.downFunctor.map (ULiftHom.down.map f)).unop.map_val.trans
      (Category.comp_id _).symm

/-- 概要：同じ全 augmentation の各成分は元の加群の擬同型。
方針：同じ半自由 frame の検証済み条件をそのまま評価する。
規約：HA §1.3.4、同じ成分。使われ方：全評価屋根の左脚の反転。 -/
lemma strictRawModuleTensorElementAugmentation_weak (s : strictRawModuleTensorElementIndex A X P Q) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementAugmentation A X P Q).app s) :=
  strictRawModuleTensorFrame_augmentation_weak A X _ (strictRawModuleProbeFunctor_semifree A X P)
    (ULiftHom.objDown s).down.unop.obj.unop

/-- 概要：同じ全評価図式の全ての作用素は元の加群の擬同型。
方針：同じ半自由 frame の全作用素の弱同値性を移送する。
規約：HA §1.3.4、全作用素。使われ方：全単体パラメータでの局所化。 -/
lemma strictRawModuleTensorElementDiagram_map_weak
    {s t : strictRawModuleTensorElementIndex A X P Q} (f : s ⟶ t) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorElementDiagram A X P Q).map f) :=
  (strictRawModuleModelCategory_weakEquivalences A X) ▸
    strictRawModuleProbeTensorFrame_homotopicallyConstant A X P
      (ULift.downFunctor.map (ULiftHom.down.map f)).unop.hom.unop

end SerrePositivity.EInfinity.BarrattEccles
