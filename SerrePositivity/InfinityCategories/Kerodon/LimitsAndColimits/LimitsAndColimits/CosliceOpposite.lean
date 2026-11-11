module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite

/-!
概要：coslice の反転を反転した図式の slice と比較する。
方針：余錐の図式を反転し、標準単体の反転同型でパラメータを戻す。
規約：図式と値域に充填性の仮定を置かない。
使われ方：左 Kan の比較余錐の普遍性を右側へ移す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐の図式の反転は反転した図式への錐の図式と同値。
方針：op の Hom 同値と join の反転同型を固定条件に制限する。
規約：パラメータ A も反転する。
使われ方：coslice の反転同型の次数ごとの構成。 -/
def coconeDiagramReverseEquiv {K X : SSet.{u}} (p : K ⟶ X) (A : SSet.{u}) :
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p} ≃
      {G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A.op K.op ⟶ X.op // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A.op K.op ≫ G = SSet.opFunctor.map p} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv K A X).subtypeEquiv (by
    intro F
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv_apply, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inr_inv,
      ← CategoryTheory.Functor.map_comp]
    exact ⟨congrArg SSet.opFunctor.map,
      SSet.opEquivalence.fullyFaithfulFunctor.map_injective⟩)

/-- 概要：錐のパラメータの同型は固定図式を保った図式の同値を与える。
方針：join の同型による Hom 同値を右端の固定条件へ制限する。
規約：右因子 K は変更しない。
使われ方：反転した標準単体から通常の標準単体へ戻す。 -/
def coneDiagramReparamEquiv {K X A B : SSet.{u}} (p : K ⟶ X) (e : A ≅ B) :
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p} ≃
      {G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B K ≫ G = p} :=
  (Iso.homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso e (Iso.refl K)) (Iso.refl X)).subtypeEquiv (by
    intro F
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap e.inv (𝟙 K) ≫ F ≫ 𝟙 X) = p
    rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp])

/-- 概要：coslice の反転と反転した図式の slice は各次数で同値。
方針：図式の反転とパラメータの正規化を合成する。
規約：標準単体の反転同型を明示する。
使われ方：単体集合の同型となる自然変換の成分。 -/
def sliceUnderOpObjEquiv {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op.obj (Opposite.op n) ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.opFunctor.map p)).obj (Opposite.op n) :=
  (SSet.opObjEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) (n := Opposite.op n)).trans
    ((coconeDiagramReverseEquiv p (stdSimplex.obj n)).trans
      (coneDiagramReparamEquiv (SSet.opFunctor.map p) (stdSimplex.opIso n)))

/-- 概要：coslice の反転の成分の射を join の逆反転で表示する。
方針：二つの Hom 同値を展開して恒等射を消去する。
規約：固定条件の証明には依存しない等式。
使われ方：単体作用との自然性と普遍錐の射の計算。 -/
lemma sliceUnderOpObjEquiv_val {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op.obj (Opposite.op n)) :
    (sliceUnderOpObjEquiv p n s).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso n).inv (𝟙 K.op) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K (stdSimplex.obj n)).inv ≫
          SSet.opFunctor.map (SSet.opObjEquiv s).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso n).inv (𝟙 K.op) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv K (stdSimplex.obj n) X (SSet.opObjEquiv s).val ≫ 𝟙 X.op = _
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv_apply]

/-- 概要：coslice の反転から反転した図式の slice への比較射。
方針：join の反転と標準単体の逆反転の自然性で成分を束ねる。
規約：追加の仮定は不要。
使われ方：余極限余錐を反転した極限錐へ移す。 -/
def sliceUnderOpMap {K X : SSet.{u}} (p : K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.opFunctor.map p) where
  app n := ↾(sliceUnderOpObjEquiv p n.unop)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (sliceUnderOpObjEquiv p ⦋m⦌ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op.map α s)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K.op) ≫ (sliceUnderOpObjEquiv p ⦋n⦌ s).val
    rw [sliceUnderOpObjEquiv_val, sliceUnderOpObjEquiv_val]
    have hs : (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op.map α s)).val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop)) ≫
          (SSet.opObjEquiv s).val := rfl
    rw [hs, SSet.opFunctor.map_comp]
    let V : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[n] : SSet.{u}) ⟶ X := (SSet.opObjEquiv s).val
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋m⦌).inv (𝟙 K.op) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[m]).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))) ≫
          SSet.opFunctor.map V =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K.op) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋n⦌).inv (𝟙 K.op) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[n]).inv ≫ SSet.opFunctor.map V
    have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality
      (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))
    simp only [CategoryTheory.Functor.map_id] at hR
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α.unop)))
      (𝟙 K.op) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[n]).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[m]).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (SimplexCategory.rev.map α.unop))) at hR
    rw [← reassoc_of% hR]
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableStdSimplex_opIso_inv_naturality]

/-- 概要：coslice の反転の比較射は同型。
方針：各次数の成分が全単射であることを使う。
規約：充填性の仮定は不要。
使われ方：普遍性を保存・反映する比較。 -/
instance sliceUnderOpMap_isIso {K X : SSet.{u}} (p : K ⟶ X) :
    IsIso (sliceUnderOpMap p) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).2 (sliceUnderOpObjEquiv p ⦋n⦌).bijective

/-- 概要：coslice の反転は反転した図式の slice と同型。
方針：比較射とその次数ごとの全単射性をまとめる。
規約：図式と標的は任意。
使われ方：余極限と極限の錐ごとの双対性。 -/
def sliceUnderOpIso {K X : SSet.{u}} (p : K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.opFunctor.map p) := asIso (sliceUnderOpMap p)

/-- 概要：余錐を反転した図式への錐として表示する。
方針：coslice の反転同型を零単体に適用する。
規約：錐の頂点の標準零単体も正規化する。
使われ方：左 Kan の普遍余錐を右側へ移す。 -/
def coconeReverseCone {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (SSet.opFunctor.map p) :=
  (sliceUnderOpIso p).hom.app (Opposite.op ⦋0⦌)
    (SSet.opObjEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋0⦌ from c))

/-- 概要：反転した錐の射は正規化した join の逆反転による前合成。
方針：coslice の反転同値の零次成分を計算する。
規約：固定条件の証明には依存しない。
使われ方：反転した輸送の終端の射と比較する。 -/
lemma coconeReverseCone_val {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (coconeReverseCone c).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 K.op) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso K Δ[0]).inv ≫ SSet.opFunctor.map c.val :=
  sliceUnderOpObjEquiv_val p ⦋0⦌ _

/-- 概要：余錐の余極限性は反転した錐の極限性と同値。
方針：coslice の始対象を反転し、slice との同型で終対象性を保存・反映する。
規約：標的の quasicategory 性を仮定しない。
使われ方：左 Kan の比較余錐の普遍性を反転後の右比較錐へ移す。 -/
lemma isColimitCone_iff_reverseCone {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (coconeReverseCone c) := by
  constructor
  · intro hc
    exact hc.op_isTerminalVertex.map_of_isIso (sliceUnderOpIso p).hom
  · intro hc
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_of_isTerminalVertex_op
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (sliceUnderOpIso p).hom hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
