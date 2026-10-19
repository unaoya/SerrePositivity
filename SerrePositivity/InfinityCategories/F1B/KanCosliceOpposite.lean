module

public import SerrePositivity.InfinityCategories.Stable.ConeOpposite

/-!
概要：coslice の反転を反転した図式の slice と比較する。
方針：余錐の図式を反転し、標準単体の反転同型でパラメータを戻す。
規約：図式と値域に充填性の仮定を置かない。
使われ方：左 Kan の比較余錐の普遍性を右側へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：余錐の図式の反転は反転した図式への錐の図式と同値。
方針：op の Hom 同値と join の反転同型を固定条件に制限する。
規約：パラメータ A も反転する。
使われ方：coslice の反転同型の次数ごとの構成。 -/
def kanCoconeDiagramReverseEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    {F : join K A ⟶ X // joinInl K A ≫ F = p} ≃
      {G : join A.op K.op ⟶ X.op // joinInr A.op K.op ≫ G = SSet.opFunctor.map p} :=
  (coneDiagramReverseHomEquiv K A X).subtypeEquiv (by
    intro F
    rw [coneDiagramReverseHomEquiv_apply, ← Category.assoc, stableJoinReverse_inr_inv,
      ← CategoryTheory.Functor.map_comp]
    exact ⟨congrArg SSet.opFunctor.map,
      SSet.opEquivalence.fullyFaithfulFunctor.map_injective⟩)

/-- 概要：錐のパラメータの同型は固定図式を保った図式の同値を与える。
方針：join の同型による Hom 同値を右端の固定条件へ制限する。
規約：右因子 K は変更しない。
使われ方：反転した標準単体から通常の標準単体へ戻す。 -/
def kanConeDiagramReparamEquiv {K X A B : SSet.{u}} (p : K ⟶ X) (e : A ≅ B) :
    {F : join A K ⟶ X // joinInr A K ≫ F = p} ≃
      {G : join B K ⟶ X // joinInr B K ≫ G = p} :=
  (Iso.homCongr (joinIso e (Iso.refl K)) (Iso.refl X)).subtypeEquiv (by
    intro F
    change (joinInr A K ≫ F = p) ↔
      joinInr B K ≫ (joinMap e.inv (𝟙 K) ≫ F ≫ 𝟙 X) = p
    rw [Category.comp_id, ← Category.assoc, joinInr_joinMap, Category.id_comp])

/-- 概要：coslice の反転と反転した図式の slice は各次数で同値。
方針：図式の反転とパラメータの正規化を合成する。
規約：標準単体の反転同型を明示する。
使われ方：単体集合の同型となる自然変換の成分。 -/
def kanSliceUnderOpObjEquiv {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory) :
    (sliceUnder p).op.obj (Opposite.op n) ≃
      (sliceOver (SSet.opFunctor.map p)).obj (Opposite.op n) :=
  (SSet.opObjEquiv (X := sliceUnder p) (n := Opposite.op n)).trans
    ((kanCoconeDiagramReverseEquiv p (stdSimplex.obj n)).trans
      (kanConeDiagramReparamEquiv (SSet.opFunctor.map p) (stdSimplex.opIso n)))

/-- 概要：coslice の反転の成分の射を join の逆反転で表示する。
方針：二つの Hom 同値を展開して恒等射を消去する。
規約：固定条件の証明には依存しない等式。
使われ方：単体作用との自然性と普遍錐の射の計算。 -/
lemma kanSliceUnderOpObjEquiv_val {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory)
    (s : (sliceUnder p).op.obj (Opposite.op n)) :
    (kanSliceUnderOpObjEquiv p n s).val =
      joinMap (stdSimplex.opIso n).inv (𝟙 K.op) ≫
        (stableJoinReverseIso K (stdSimplex.obj n)).inv ≫
          SSet.opFunctor.map (SSet.opObjEquiv s).val := by
  change joinMap (stdSimplex.opIso n).inv (𝟙 K.op) ≫
    coneDiagramReverseHomEquiv K (stdSimplex.obj n) X (SSet.opObjEquiv s).val ≫ 𝟙 X.op = _
  rw [Category.comp_id, coneDiagramReverseHomEquiv_apply]

/-- 概要：coslice の反転から反転した図式の slice への比較射。
方針：join の反転と標準単体の逆反転の自然性で成分を束ねる。
規約：追加の仮定は不要。
使われ方：余極限余錐を反転した極限錐へ移す。 -/
def kanSliceUnderOpMap {K X : SSet.{u}} (p : K ⟶ X) :
    (sliceUnder p).op ⟶ sliceOver (SSet.opFunctor.map p) where
  app n := ↾(kanSliceUnderOpObjEquiv p n.unop)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (kanSliceUnderOpObjEquiv p ⦋m⦌ ((sliceUnder p).op.map α s)).val =
      joinMap (stdSimplex.map α.unop) (𝟙 K.op) ≫ (kanSliceUnderOpObjEquiv p ⦋n⦌ s).val
    rw [kanSliceUnderOpObjEquiv_val, kanSliceUnderOpObjEquiv_val]
    have hs : (SSet.opObjEquiv ((sliceUnder p).op.map α s)).val =
        joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop)) ≫
          (SSet.opObjEquiv s).val := rfl
    rw [hs, SSet.opFunctor.map_comp]
    let V : join K (Δ[n] : SSet.{u}) ⟶ X := (SSet.opObjEquiv s).val
    change joinMap (stdSimplex.opIso ⦋m⦌).inv (𝟙 K.op) ≫
      (stableJoinReverseIso K Δ[m]).inv ≫
        SSet.opFunctor.map (joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))) ≫
          SSet.opFunctor.map V =
      joinMap (stdSimplex.map α.unop) (𝟙 K.op) ≫
        joinMap (stdSimplex.opIso ⦋n⦌).inv (𝟙 K.op) ≫
          (stableJoinReverseIso K Δ[n]).inv ≫ SSet.opFunctor.map V
    have hR := stableJoinReverse_inv_naturality
      (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))
    simp only [CategoryTheory.Functor.map_id] at hR
    change joinMap (SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α.unop)))
      (𝟙 K.op) ≫ (stableJoinReverseIso K Δ[n]).inv =
      (stableJoinReverseIso K Δ[m]).inv ≫
        SSet.opFunctor.map (joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))) at hR
    rw [← reassoc_of% hR]
    simp only [← Category.assoc, ← joinMap_comp, Category.comp_id]
    rw [stableStdSimplex_opIso_inv_naturality]

/-- 概要：coslice の反転の比較射は同型。
方針：各次数の成分が全単射であることを使う。
規約：充填性の仮定は不要。
使われ方：普遍性を保存・反映する比較。 -/
instance kanSliceUnderOpMap_isIso {K X : SSet.{u}} (p : K ⟶ X) :
    IsIso (kanSliceUnderOpMap p) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).2 (kanSliceUnderOpObjEquiv p ⦋n⦌).bijective

/-- 概要：coslice の反転は反転した図式の slice と同型。
方針：比較射とその次数ごとの全単射性をまとめる。
規約：図式と標的は任意。
使われ方：余極限と極限の錐ごとの双対性。 -/
def kanSliceUnderOpIso {K X : SSet.{u}} (p : K ⟶ X) :
    (sliceUnder p).op ≅ sliceOver (SSet.opFunctor.map p) := asIso (kanSliceUnderOpMap p)

/-- 概要：余錐を反転した図式への錐として表示する。
方針：coslice の反転同型を零単体に適用する。
規約：錐の頂点の標準零単体も正規化する。
使われ方：左 Kan の普遍余錐を右側へ移す。 -/
def kanCoconeReverseCone {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    JoinCone (SSet.opFunctor.map p) :=
  (kanSliceUnderOpIso p).hom.app (Opposite.op ⦋0⦌)
    (SSet.opObjEquiv.symm (show (sliceUnder p) _⦋0⦌ from c))

/-- 概要：反転した錐の射は正規化した join の逆反転による前合成。
方針：coslice の反転同値の零次成分を計算する。
規約：固定条件の証明には依存しない。
使われ方：反転した輸送の終端の射と比較する。 -/
lemma kanCoconeReverseCone_val {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    (kanCoconeReverseCone c).val =
      joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op) ≫
        (stableJoinReverseIso K Δ[0]).inv ≫ SSet.opFunctor.map c.val :=
  kanSliceUnderOpObjEquiv_val p ⦋0⦌ _

/-- 概要：余錐の余極限性は反転した錐の極限性と同値。
方針：coslice の始対象を反転し、slice との同型で終対象性を保存・反映する。
規約：標的の quasicategory 性を仮定しない。
使われ方：左 Kan の比較余錐の普遍性を反転後の右比較錐へ移す。 -/
lemma kanIsColimitCone_iff_reverseCone {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) : IsColimitCone c ↔ IsLimitCone (kanCoconeReverseCone c) := by
  constructor
  · intro hc
    exact hc.op_isTerminalVertex.map_of_isIso (kanSliceUnderOpIso p).hom
  · intro hc
    apply isInitialVertex_of_isTerminalVertex_op
    exact isTerminalVertex_of_trivialKanFibration (kanSliceUnderOpIso p).hom hc

end SerrePositivity.InfinityCategories.F1B
