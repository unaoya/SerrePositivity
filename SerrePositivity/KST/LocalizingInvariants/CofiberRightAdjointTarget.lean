module

public import SerrePositivity.KST.LocalizingInvariants.CofiberAdjunction

/-!
概要：cofiber の実右随伴の矢印の終域は、元の入力対象そのものである。
方針：四角形の共通角、右辺切断の厳密性、恒等矢印の始点評価を使う。
規約：全単体上の厳密な等式。使われ方：右随伴を零始点矢印として同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma cofiber_diagram_right_vertex (X : SSet.{u}) (z : (CofiberDiagrams.space X) _⦋0⦌) :
    (CofiberDiagrams.right X).app (Opposite.op ⦋0⦌) z =
      functorVertex (squareRightEdge ≫ squareDiagram z.val) := by
  have hz : functorVertex (squareDiagram z.val) = z.val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change ((pre squareRightEdge).app X).app (Opposite.op ⦋0⦌) z.val = _
  rw [← hz]
  rfl

lemma cofiber_diagram_bottom_source (X : SSet.{u}) (z : (CofiberDiagrams.space X) _⦋0⦌) :
    (CofiberDiagrams.bottom X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) z =
        squareVertex (squareDiagram z.val) 0 0 := by
  have hz : functorVertex (squareDiagram z.val) = z.val :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (evaluateFunctorAt _).app (Opposite.op ⦋0⦌)
    (((pre squareBottomEdge).app X).app (Opposite.op ⦋0⦌) z.val) = _
  rw [← hz]
  rfl

lemma cofiber_bottom_target_eq_right_source (X : SSet.{u}) :
    CofiberDiagrams.bottom X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      CofiberDiagrams.right X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  simp only [CofiberDiagrams.bottom, CofiberDiagrams.right, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

lemma identityArrow_source (X : SSet.{u}) :
    ArrowTarget.identityArrow X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      𝟙 X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  change X.map (𝟙 n) x = x
  exact CategoryTheory.Functor.map_id_apply X n x

/-- 元の入力対象は右随伴の矢印の終域に全単体上で厳密に残る。 -/
lemma cofiberRightAdjoint_target (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    cofiberRightAdjoint X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      𝟙 X := by
  simp only [cofiberRightAdjoint, CofiberRotation.inverseRotation, Category.assoc]
  rw [cofiber_bottom_target_eq_right_source]
  rw [← Category.assoc (CofiberRotation.rightSection X), CofiberRotation.rightSection_right,
    Category.id_comp]
  exact identityArrow_source X

end SerrePositivity.KST.LocalizingInvariants
