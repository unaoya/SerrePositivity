module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeOppositeExistence
public import SerrePositivity.InfinityCategories.F1B.KanRelativeRightCanonical
public import SerrePositivity.InfinityCategories.F1B.KanCoconeFamilyDiagramEq

/-!
概要：右 Kan の標準局所相対極限の存在を反転前の左の局所相対余極限へ移す。
方針：局所添字の反転同型で錐を制限し、coslice の反転同型を逆に使う。
規約：標準底錐の全体への像を厳密な等式として保つ。
使われ方：右の相対厳密な存在の左の存在定理への帰着。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：反転した右の標準底錐上の相対極限から左の標準底余錐上の相対余極限が存在する。
方針：局所添字の同型で極限錐を制限し、反転を戻して底の標準余錐の像を回収する。
規約：元と底の図式は等式で両立させる。
使われ方：標準局所相対存在仮定の双対化。 -/
lemma exists_kanRelativeLeftLocalColimit_of_op_rightLimit {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C)
    (F₀ : K ⟶ D) (H₀ : C ⟶ E) (hFU : F₀ ≫ U = δ ≫ H₀) (c : C _⦋0⦌)
    (z : JoinCone (rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opObjEquiv.symm c)))
    (hz : IsRelativeLimitCone (SSet.opFunctor.map U) z)
    (hzu : z.val ≫ SSet.opFunctor.map U =
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map H₀)
        (SSet.opObjEquiv.symm c)).val) :
    ∃ d : JoinCocone (leftKanDiagram δ F₀ c), IsRelativeColimitCone U d ∧
      d.val ≫ U = (leftKanCanonicalCocone δ H₀ c).val := by
  let e := kanLeftKanShapeOpIso δ c
  let p := leftKanDiagram δ F₀ c
  let q := rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
    (SSet.opObjEquiv.symm c)
  have hp : e.hom ≫ q = SSet.opFunctor.map p := by
    dsimp only [e, q, p, rightKanDiagram, leftKanDiagram]
    rw [← Category.assoc, kanLeftKanShapeOpIso_projection, Functor.map_comp]
  let a : JoinCone (SSet.opFunctor.map p) :=
    ⟨joinMap (𝟙 (Δ[0] : SSet.{u})) e.hom ≫ z.val, by
      rw [← Category.assoc, joinInr_joinMap, Category.assoc, z.property]
      exact hp⟩
  have ha : IsRelativeLimitCone (SSet.opFunctor.map U) a := by
    have h := (kanIsRelativeLimitCone_iff_restrict_of_isIso (SSet.opFunctor.map U) z e.hom).1 hz
    exact (kanIsRelativeLimitCone_congr (SSet.opFunctor.map U) hp _ a rfl).1 h
  have hb : leftKanDiagram δ (δ ≫ H₀) c = p ≫ U := by
    dsimp only [p, leftKanDiagram]
    rw [Category.assoc, hFU]
  let b := kanCoconeOfDiagramEq hb (leftKanCanonicalCocone δ H₀ c)
  have hab : a.val ≫ SSet.opFunctor.map U = (kanCoconeReverseCone b).val := by
    change (joinMap (𝟙 (Δ[0] : SSet.{u})) e.hom ≫ z.val) ≫ SSet.opFunctor.map U = _
    rw [Category.assoc, hzu, ← kanLocalConeOppositeIso_canonical δ H₀ c,
      kanCoconeReverseCone_val]
    dsimp only [b, kanCoconeOfDiagramEq, kanLocalConeOppositeIso, Iso.trans_inv, joinIso, e]
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.hom_inv_id]
  exact exists_kanRelativeColimit_of_op_relative_limit p U b a ha hab

end SerrePositivity.InfinityCategories.F1B
