module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentFibrations
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentFibers

/-!
概要：既存部分の指定 Hom を延長する両側の同じ空間は Kan 複体。
方針：同じ元の制限の Kan fibration 性を固定値の fiber へ移す。
規約：貼付け写像の単射性や元の Hom の延長可能性は仮定しない。
使われ方：骨格降下で比較する実際の境界固定の延長空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {B : SSet.{u}} {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left) [Mono f.left]

include hp in
/-- 元の既存部分の Hom を固定した、全 source Hom の延長空間は Kan。 -/
lemma cocartesianCellAttachment_sourceExtension_kanComplex
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    (r : ((SSet.uliftFunctor.{u + 1, u}).obj
      ((cocartesianPullbackNativeCoreFunctor p q).obj (Opposite.op c))) _⦋0⦌) :
    KanComplex (vertexFiber (cocartesianPullbackNativeLiftPre p q j) r) := by
  letI := cocartesianCellAttachment_nativeRestriction_fibration f g i j hp p q
  exact vertexFiber_kanComplex_of_leftFibration _ _

include hp in
/-- 分類先の同じ既存部分の指定値の延長空間も Kan。 -/
lemma cocartesianCellAttachment_targetExtension_kanComplex
    {X : SSet.{u + 1}} [Quasicategory X] (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X)
    (r : ((intervalDiagramOverFunctor P Q).obj
      (Opposite.op (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map c.hom)))) _⦋0⦌) :
    KanComplex (vertexFiber (intervalDiagramOverPre P Q (uliftOverMorphism j)) r) := by
  letI := cocartesianCellAttachment_intervalRestriction_fibration f g i j hp P Q
  exact vertexFiber_kanComplex_of_leftFibration _ _

end SerrePositivity.InfinityCategories
