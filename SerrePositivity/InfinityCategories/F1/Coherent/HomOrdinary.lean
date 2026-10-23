module

public import SerrePositivity.InfinityCategories.F1.Coherent.HomNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv

/-!
概要：coherent Hom 比較射の通常の射に対応する零単体での値。
方針：一単体の射データを抽出し、端点と一点の豊穣 Hom の評価を比較する。
規約：局所 Kan 性は不要。
使われ方：Kerodon Construction 4.6.7.3、写像空間の比較と通常の射の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：豊穣 Hom の通常の射の頂点は、その射の coherent な辺へ写る。
方針：一単体の端点付き射データの同値で比較する。
規約：比較射の入力では Hom の宇宙を持ち上げる。
使われ方：Kerodon Construction 4.6.7.3、空間値分類の写像空間比較の零次の同定。 -/
lemma coherentHomComparison_ordinary {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f : X ⟶ Y) :
    ((coherentHomComparison X Y).app (Opposite.op ⦋0⦌)
      (ULift.up (SimplicialCategory.homEquiv' X Y f))).val =
        (coherentNerveEdge f).edge := by
  apply (coherentNerveArrowDataEquiv C).injective
  change coherentNerveArrowData _ = coherentNerveArrowData _
  rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow]
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm _⟩ : Σ A B : C, A ⟶ B) =
    ⟨X, Y, f⟩
  congr 2
  apply (SimplicialCategory.homEquiv' X Y).injective
  rw [Equiv.apply_symm_apply]
  change (SSet.yonedaEquiv.symm (SimplicialCategory.homEquiv' X Y f)).app
    (Opposite.op ⦋0⦌) _ = _
  have h : (pathLastMaximumMap (0 : Fin 1)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentOnePath) = ULift.up (𝟙 ⦋0⦌) := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  exact (congrArg (fun z : (Δ[0] : SSet.{u}) _⦋0⦌ ↦
    (SSet.yonedaEquiv.symm (SimplicialCategory.homEquiv' X Y f)).app
      (Opposite.op ⦋0⦌) z) h).trans (Equiv.apply_symm_apply SSet.yonedaEquiv _)

end SerrePositivity.InfinityCategories
