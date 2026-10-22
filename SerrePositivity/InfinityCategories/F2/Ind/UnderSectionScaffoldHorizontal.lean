module

public import SerrePositivity.InfinityCategories.F2.Ind.ProductIndexCocartesian
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionScaffoldValue
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianScaffold

/-!
概要：元の under scaffold の水平辺は、元の添字への射影に関して cocartesian。
方針：元の底パラメータが定値であることを計算し、積の第二射影の判定と合成する。
規約：元の全空間と元の大域射を使う。水平辺の像を選び直さない。
使われ方：大域 under scaffold の前合成同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} (p : E ⟶ B ⊗ nerve I)

/-- 水平辺上の元のパラメータは、始点の元のパラメータに定値。 -/
lemma underSectionScaffold_horizontal_parameter {i j : I} (f : i ⟶ j)
    (x : underSectionFamily p i _⦋0⦌) :
    (p ≫ fst B (nerve I)).app (Opposite.op ⦋1⦌)
      ((underSectionScaffold p).app _
        (kanScaffoldHorizontalEdge (underSectionTotalDiagram p) f x)) =
      PinchedHom.constant ((underSectionFamilyProjection p i).app _ x) 1 := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (underSectionScaffold_fst p) (Opposite.op ⦋1⦌))
    (kanScaffoldHorizontalEdge (underSectionTotalDiagram p) f x)
  change _ = SSet.yonedaEquiv
    ((SSet.const x : (Δ[1] : SSet.{u}) ⟶ underSectionFamily p i) ≫
      underSectionFamilyProjection p i) at h
  rw [SSet.const_comp] at h
  exact h

/-- 同じ水平辺の同じ大域像は、元の添字に関して cocartesian。 -/
lemma underSectionScaffold_horizontal [Quasicategory B] [LeftFibration p]
    {i j : I} (f : i ⟶ j) (x : underSectionFamily p i _⦋0⦌) :
    IsCocartesianEdge (p ≫ snd B (nerve I))
      ((underSectionScaffold p).app _
        (kanScaffoldHorizontalEdge (underSectionTotalDiagram p) f x)) := by
  apply (isCocartesianEdge_of_leftFibration p _).comp
  apply F1B.kanIsCocartesianEdge_productSnd_of_invertible
  change IsInvertibleEdge (edgeOfSimplex ((p ≫ fst B (nerve I)).app _ _))
  rw [underSectionScaffold_horizontal_parameter]
  exact F1B.kanConstantEdge_isInvertible _

instance underSectionTotalDiagram_quasicategory [Quasicategory B] [LeftFibration p] (i : I) :
    Quasicategory ((underSectionTotalDiagram p).obj i) :=
  underSectionFamily_quasicategory p i

end SerrePositivity.InfinityCategories.F2.Ind
