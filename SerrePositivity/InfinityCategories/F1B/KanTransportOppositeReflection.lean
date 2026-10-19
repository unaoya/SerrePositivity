module

public import SerrePositivity.InfinityCategories.F1B.KanTransportOppositeUniversality
public import SerrePositivity.InfinityCategories.F1B.KanComparisonCocartesian

/-!
概要：左 Kan の局所余錐の反転は普遍性を反映する。
方針：反転した局所錐の添字の同型を戻し、余錐の反転との普遍性の同値を使う。
規約：標的の quasicategory 性は不要。
使われ方：右 Kan 条件から反転した左 Kan 条件への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：反転した右輸送の比較錐が極限なら元の左比較余錐は余極限。
方針：局所添字の同型に沿う制限が終対象性を反映することを使い、反転前へ戻す。
規約：指定した局所輸送そのものを比較する。
使われ方：Kan 条件の双対化の逆方向。 -/
lemma kanCoconeTransportOpposite_isColimit_of_isLimit {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) (h : IsLimitCone (kanCoconeTransportOpposite t).cone) :
    IsColimitCone t.cocone := by
  let e := kanLeftKanShapeOpIso δ c
  let p := SSet.opFunctor.map (leftKanDiagram δ F₀ c)
  let d : JoinCone (e.inv ≫ p) :=
    (sliceOverRestrict p e.inv).app (Opposite.op ⦋0⦌) (kanCoconeReverseCone t.cocone)
  have hp : e.inv ≫ p = rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opObjEquiv.symm c) := by
    dsimp only [p, leftKanDiagram, rightKanDiagram]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← kanLeftKanShapeOpIso_projection, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hv : d.val = (kanCoconeTransportOpposite t).cone.val := by
    change joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫
      (kanCoconeReverseCone t.cocone).val = (kanCoconeTransportOpposite t).cone.val
    rw [kanCoconeReverseCone_val, kanCoconeTransportOpposite_cone_val]
    dsimp only [kanLocalConeOppositeIso, Iso.trans_inv, joinIso, e]
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
  have hd : IsLimitCone d := kanIsLimitCone_of_diagram_eq hp.symm hv.symm h
  have := sliceOverRestrict_isIso p e.inv
  apply (kanIsColimitCone_iff_reverseCone t.cocone).2
  exact isTerminalVertex_of_trivialKanFibration (sliceOverRestrict p e.inv) hd

/-- 概要：左局所余錐の普遍性は反転した右局所錐の普遍性と同値。
方針：反転による保存と反映を組み合わせる。
規約：元の輸送と指定変換を保つ。
使われ方：左右 Kan 条件の反転による判定。 -/
lemma kanCoconeTransportOpposite_isLimit_iff {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    IsColimitCone t.cocone ↔ IsLimitCone (kanCoconeTransportOpposite t).cone :=
  ⟨kanCoconeTransportOpposite_isLimit t, kanCoconeTransportOpposite_isColimit_of_isLimit t⟩

/-- 概要：左 Kan 条件は指定変換を反転した右 Kan 条件と同値。
方針：保存方向には輸送を反転し、反映方向には任意の左輸送の反転の極限性を回収する。
規約：標的 D のみ quasicategory とする。
使われ方：指定変換を保持した Kan 条件の双対化。 -/
lemma kanIsLeftKanExtension_iff_opposite {K C D : SSet.{u}} [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (F : C ⟶ D) (β : SSet.Homotopy F₀ (δ ≫ F)) :
    IsLeftKanExtension δ F₀ F β ↔
      IsRightKanExtension (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opFunctor.map F) (kanLeftOppositeTransformation δ F₀ F β) := by
  constructor
  · exact kanIsLeftKanExtension_opposite
  · intro h c
    obtain ⟨t⟩ := leftKanCoconeTransport_nonempty δ F₀ F β c
    have ht := (isRightKanExtension_iff_forall_transport _ _ _ _).1 h
      (SSet.opObjEquiv.symm c) (kanCoconeTransportOpposite t)
    exact ⟨t, kanCoconeTransportOpposite_isColimit_of_isLimit t ht⟩

end SerrePositivity.InfinityCategories.F1B
