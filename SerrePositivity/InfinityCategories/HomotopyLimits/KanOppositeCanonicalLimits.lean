module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LocalCanonicalConeOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.TransportOppositeUniversality

/-!
概要：元の左 Kan 標準全余錐の余極限性を、反転した元の右 Kan 標準全錐へ移す。
方針：全余錐を反転し、元の局所添字の厳密な同型に沿って制限する。
規約：標準全写像の厳密な一致を使い、端点や普遍対象だけの比較に縮約しない。
使われ方：元の左 Kan 延長の Hom 全族を、実際の右 Kan 条件へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F1B

/-- 元の標準左 Kan 全余錐が余極限なら、反転した同じ標準右 Kan 全錐は極限。 -/
lemma rightKanCanonicalCone_op_isLimit {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌)
    (hc : IsColimitCone (leftKanCanonicalCocone δ F c)) :
    IsLimitCone (rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
      (SSet.opObjEquiv.symm c)) := by
  let e := kanLeftKanShapeOpIso δ c
  let p := SSet.opFunctor.map (leftKanDiagram δ (δ ≫ F) c)
  let d : JoinCone (e.inv ≫ p) := (sliceOverRestrict p e.inv).app (Opposite.op ⦋0⦌)
    (SerrePositivity.InfinityCategories.F1B.coconeReverseCone (leftKanCanonicalCocone δ F c))
  have := sliceOverRestrict_isIso p e.inv
  have hd : IsLimitCone d := ((SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone _).mp hc).map_of_isIso
    (sliceOverRestrict p e.inv)
  have hp : e.inv ≫ p = rightKanDiagram (SSet.opFunctor.map δ)
      (SSet.opFunctor.map δ ≫ SSet.opFunctor.map F) (SSet.opObjEquiv.symm c) := by
    dsimp only [e, p, leftKanDiagram, rightKanDiagram]
    rw [Functor.map_comp, Functor.map_comp, ← kanLeftKanShapeOpIso_projection]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply kanIsLimitCone_of_diagram_eq hp _ hd
  change joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫
    (SerrePositivity.InfinityCategories.F1B.coconeReverseCone (leftKanCanonicalCocone δ F c)).val = _
  rw [SerrePositivity.InfinityCategories.F1B.coconeReverseCone_val]
  have he : joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫
      joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 (leftKanShape δ c).op) ≫
        (stableJoinReverseIso (leftKanShape δ c) Δ[0]).inv =
      (kanLocalConeOppositeIso δ c).inv := by
    dsimp only [e, kanLocalConeOppositeIso, Iso.trans_inv, joinIso]
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
  simp only [← Category.assoc] at he ⊢
  rw [he, kanLocalConeOppositeIso_canonical]

end SerrePositivity.InfinityCategories.HomotopyLimits
