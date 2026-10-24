module

public import SerrePositivity.InfinityCategories.F1B.Cones.CosliceOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.CoconeTransportOpposite
public import SerrePositivity.InfinityCategories.Core.SliceRestriction

/-!
概要：反転した局所輸送の錐へ元の余錐の普遍性を移す。
方針：余錐の反転による極限性を局所添字の同型に沿って移し、輸送の終端と同定する。
規約：指定変換そのものを保持し、頂点だけの条件へ弱めない。
使われ方：左 Kan 条件から反転後の右 Kan 条件への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：図式の等式で同じ射を持つ錐へ極限性を移す。
方針：図式の等式を消去し、錐の部分型の外延性を使う。
規約：錐全体の射の等式を要求する。
使われ方：反転と添字の正規化による型の変更。 -/
lemma kanIsLimitCone_of_diagram_eq {A X : SSet.{u}} {p q : A ⟶ X}
    {c : JoinCone p} {d : JoinCone q} (hp : p = q) (hc : c.val = d.val)
    (h : IsLimitCone c) : IsLimitCone d := by
  subst q
  have he : c = d := Subtype.ext hc
  rwa [← he]

/-- 概要：元の左輸送の余錐が普遍なら反転した右輸送の錐も普遍。
方針：余錐の反転を局所添字の同型の逆へ制限し、終端の射の等式を使う。
規約：quasicategory 性は不要。
使われ方：指定変換を保った左右 Kan 条件の双対化。 -/
lemma kanCoconeTransportOpposite_isLimit {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) (ht : IsColimitCone t.cocone) :
    IsLimitCone (kanCoconeTransportOpposite t).cone := by
  let e := kanLeftKanShapeOpIso δ c
  let p := SSet.opFunctor.map (leftKanDiagram δ F₀ c)
  let d : JoinCone (e.inv ≫ p) :=
    (sliceOverRestrict p e.inv).app (Opposite.op ⦋0⦌) (SerrePositivity.InfinityCategories.F1B.coconeReverseCone t.cocone)
  have := sliceOverRestrict_isIso p e.inv
  have hd : IsLimitCone d :=
    ((SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone t.cocone).1 ht).map_of_isIso
      (sliceOverRestrict p e.inv)
  have hp : e.inv ≫ p =
      rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opObjEquiv.symm c) := by
    dsimp only [p, leftKanDiagram, rightKanDiagram]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← kanLeftKanShapeOpIso_projection, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply kanIsLimitCone_of_diagram_eq hp _ hd
  change joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫
    (SerrePositivity.InfinityCategories.F1B.coconeReverseCone t.cocone).val = (kanCoconeTransportOpposite t).cone.val
  rw [SerrePositivity.InfinityCategories.F1B.coconeReverseCone_val, kanCoconeTransportOpposite_cone_val]
  dsimp only [kanLocalConeOppositeIso, Iso.trans_inv, joinIso, e]
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：左 Kan の指定変換を反転すると右 Kan の指定変換となる。
方針：各頂点の左輸送を反転し、余極限性から極限性への移送を使う。
規約：単体集合や標的に追加の充填性の仮定は不要。
使われ方：左の存在定理の双対化。 -/
lemma kanIsLeftKanExtension_opposite {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)}
    (h : IsLeftKanExtension δ F₀ F β) :
    IsRightKanExtension (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opFunctor.map F) (kanLeftOppositeTransformation δ F₀ F β) := by
  intro c
  obtain ⟨t, ht⟩ := h (SSet.opObjEquiv c)
  exact ⟨kanCoconeTransportOpposite t, kanCoconeTransportOpposite_isLimit t ht⟩

end SerrePositivity.InfinityCategories.F1B
