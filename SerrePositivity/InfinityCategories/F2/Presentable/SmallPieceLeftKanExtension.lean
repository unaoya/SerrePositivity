module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPieceKanIndex
public import SerrePositivity.InfinityCategories.F2.Presentable.Accessible
public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.F1B.KanLeftCommaCoconeColimit

/-!
概要：元の全空間上の図式を、部分添字への射影に沿って coherent に左 Kan 延長する。
方針：小さい κ-filtered 局所添字の余極限を宇宙同型で移し、F1B の存在定理を適用する。
規約：元の図式と全単位変換を保持。延長の値を個別に選ぶだけでは済ませない。
使われ方：濃度変更の部分余極限の coherent な族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] {I : Type u} [PartialOrder I]
  {C : SSet.{u + 1}} [Quasicategory C]

/-- 各点の元の局所 Kan 図式は、小さい κ-filtered 余極限の存在だけで余極限を持つ。 -/
lemma smallPiece_leftKanDiagram_hasColimit (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredTotal κ μ I)) ⟶ C)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredPieces κ μ I))) _⦋0⦌) :
    HasColimit (leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece)) F v) := by
  rcases v with ⟨v⟩
  obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective v
  let p := nerveMap (smallFilteredTotalPiece (κ := κ) (μ := μ) (I := I))
  have := smallPiece_leftKanShape_isKappaFiltered A
  let e := Idempotent.leftKanShapeUniverseIso.{u, u + 1} p (nerveVertex A)
  have he : e.hom ≫ leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map p) F
      (ULift.up (nerveVertex A)) =
      (SSet.uliftFunctor.{u + 1, u}).map (leftKanProjection p (nerveVertex A)) ≫ F := by
    dsimp only [leftKanDiagram]
    rw [← Category.assoc, Idempotent.leftKanShapeUniverseIso_projection]
  have hsmall : HasColimit (e.hom ≫
      leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map p) F (ULift.up (nerveVertex A))) := by
    rw [he]
    exact hC (leftKanShape p (nerveVertex A)) _
  exact Ind.hasColimit_of_equivalentRestriction e.hom
    (qCatEquivalenceOfIso e).isQCatEquivalence _ hsmall

/-- 部分添字への元の射影に沿う、一つの全単位変換を持つ coherent な左 Kan 拡張の存在。 -/
lemma smallPiece_exists_leftKanExtension (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredTotal κ μ I)) ⟶ C) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (SmallFilteredPieces κ μ I)) ⟶ C)
      (β : SSet.Homotopy F
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece) ≫ G)),
      IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap smallFilteredTotalPiece)) F G β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ F (smallPiece_leftKanDiagram_hasColimit hC F)

end SerrePositivity.InfinityCategories.F2.Presentable
