module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismPoint

/-!
概要：元の C 全族の指定点制限は、元の同じ評価 comma の C 側の全図式そのもの。
方針：内部 Hom の宇宙比較と元の指定点での全評価を照合する。
規約：Yoneda 像による代用をせず、元の C 全係数の等号を示す。
使われ方：再構成した終点族と元の極大点評価の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の関手空間の宇宙比較は元の指定点での全評価を厳密に保つ。
方針：全次数の同じ評価を計算。規約：全係数の等号。使われ方：元の C 側の評価。 -/
lemma diagramFunctorSpace_evaluate {K C : SSet.{u}} (k : K _⦋0⦌) :
    (uliftFunctorSpaceIso K C).hom ≫ evaluateFunctorAt (Y :=
      (SSet.uliftFunctor.{u + 1, u}).obj C) (ULift.up k) =
    (SSet.uliftFunctor.{u + 1, u}).map (evaluateFunctorAt (Y := C) k) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl
/-- 概要：元の右向き C 全族の指定点制限は、元の評価族の C 全図式そのもの。
方針：元の curry と宇宙比較の全評価。規約：全射の等号。使われ方：極大点評価の同定。 -/
lemma diagramCommaOriginalFamily_point (κ : Cardinal.{u}) {K C : SSet.{u}}
    [Quasicategory C] (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) (k : K _⦋0⦌) :
    q ≫ diagramCommaEvaluation κ D k ≫ leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up k)) =
    tensorRightPoint T (diagramShapePoint k) ≫ diagramCommaOriginalFamily κ D q := by
  conv_rhs =>
    rw [diagramCommaOriginalFamily, tensorRightPoint, ← Category.assoc,
      lift_braiding_hom, diagramShapePoint, Equiv.apply_symm_apply,
      ← curry_evaluateFunctorAt_vertex, curry_uncurry]
  rw [diagramCommaEvaluation_projection]
  simp only [Category.assoc, diagramFunctorSpace_evaluate]
end SerrePositivity.InfinityCategories.F2.Ind
