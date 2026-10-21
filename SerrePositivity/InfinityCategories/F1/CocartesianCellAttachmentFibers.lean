module

public import SerrePositivity.InfinityCategories.F1.CocartesianCellAttachmentPullbacks
public import SerrePositivity.InfinityCategories.F1.VertexFiberIsPullbackIso
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramColimitCone

/-!
概要：既存部分の Hom を固定したセル付加の延長空間を、同じ局所の境界固定 fiber に同定する。
方針：同じ両側の厳密な pullback に、射影を保つ fiber 同型を適用する。
規約：元の全 Hom と既存部分の指定値を全パラメーターで保持する。
使われ方：セルと骨格の降下で同じ元の Hom 作用の相対比較を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {B : SSet.{u}} {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left)

section Source
variable {E F : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] [Mono f.left]
  (r : ((SSet.uliftFunctor.{u + 1, u}).obj
    ((cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op c))) _⦋0⦌)

/-- 指定した元の既存部分の Hom の延長空間は、同じセルの境界固定 fiber。 -/
def cocartesianCellAttachment_sourceExtensionFiberIso :
    vertexFiber (cocartesianPullbackNativeLiftPre p q j) r ≅
      vertexFiber (cocartesianPullbackNativeLiftPre p q f)
        ((cocartesianPullbackNativeLiftPre p q g).app (Opposite.op ⦋0⦌) r) :=
  vertexFiberIsoOfIsPullback (cocartesianCellAttachment_nativeLift_isPullback f g i j hp p q) r

/-- 同じ source 延長空間の同型は、元のセルへの直接制限を保持する。 -/
lemma cocartesianCellAttachment_sourceExtensionFiberIso_hom_ι :
    (cocartesianCellAttachment_sourceExtensionFiberIso f g i j hp p q r).hom ≫
      vertexFiberι (cocartesianPullbackNativeLiftPre p q f)
        ((cocartesianPullbackNativeLiftPre p q g).app (Opposite.op ⦋0⦌) r) =
    vertexFiberι (cocartesianPullbackNativeLiftPre p q j) r ≫
      cocartesianPullbackNativeLiftPre p q i :=
  vertexFiberIsoOfIsPullback_hom_ι
    (cocartesianCellAttachment_nativeLift_isPullback f g i j hp p q) r
end Source

section Target
variable {X : SSet.{u + 1}} (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)
  (r : ((intervalDiagramOverFunctor P Q).obj
    (Opposite.op (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map c.hom)))) _⦋0⦌)

/-- 分類先の指定値の延長空間も、同じセルの境界固定の区間 Hom fiber。 -/
def cocartesianCellAttachment_targetExtensionFiberIso :
    vertexFiber (intervalDiagramOverPre P Q (uliftOverMorphism j)) r ≅
      vertexFiber (intervalDiagramOverPre P Q (uliftOverMorphism f))
        ((intervalDiagramOverPre P Q (uliftOverMorphism g)).app (Opposite.op ⦋0⦌) r) :=
  vertexFiberIsoOfIsPullback (cocartesianCellAttachment_interval_isPullback f g i j hp P Q) r

/-- 同じ target 延長空間の同型も、元のセルへの直接制限を保持する。 -/
lemma cocartesianCellAttachment_targetExtensionFiberIso_hom_ι :
    (cocartesianCellAttachment_targetExtensionFiberIso f g i j hp P Q r).hom ≫
      vertexFiberι (intervalDiagramOverPre P Q (uliftOverMorphism f))
        ((intervalDiagramOverPre P Q (uliftOverMorphism g)).app (Opposite.op ⦋0⦌) r) =
    vertexFiberι (intervalDiagramOverPre P Q (uliftOverMorphism j)) r ≫
      intervalDiagramOverPre P Q (uliftOverMorphism i) :=
  vertexFiberIsoOfIsPullback_hom_ι
    (cocartesianCellAttachment_interval_isPullback f g i j hp P Q) r
end Target

end SerrePositivity.InfinityCategories
