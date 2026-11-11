module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeDiagramReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

/-! # slice の反転と coslice

概要：図式 p の slice の反転を、反転した図式の coslice と比較する。
方針：錐の図式の反転と標準単体の反転同型を各次数で合成する。
規約：値域は任意。使われ方：S4 の引き戻し側への双対化。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：標準単体の逆反転同型は反転した順序写像の射と可換。
方針：Yoneda の同値で標準単体の頂点ごとに二重反転を計算する。
規約：α は任意の単体圏の射。使われ方：slice の反転の単体作用。 -/
lemma stableStdSimplex_opIso_inv_naturality {a b : SimplexCategory} (α : a ⟶ b) :
    (stdSimplex.opIso.{u} a).inv ≫ SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α)) =
      stdSimplex.map α ≫ (stdSimplex.opIso b).inv := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro i
  change (α.toOrderHom i.rev.rev.rev).rev = (α.toOrderHom i.rev).rev
  rw [Fin.rev_rev]

/-- 概要：余錐のパラメーターの同型は固定図式を変えずに余錐の型の同値を誘導する。
方針：join の同型による Hom の同値を固定条件へ制限する。
規約：p は任意、e はパラメーターの同型。使われ方：標準単体の反転からの復帰。 -/
def cosliceDiagramReparamEquiv {K X A B : SSet.{u}} (p : K ⟶ X) (e : A ≅ B) :
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p} ≃
      {G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K B ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K B ≫ G = p} :=
  (Iso.homCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl K) e) (Iso.refl X)).subtypeEquiv (by
    intro F
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K B ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) e.inv ≫ F ≫ 𝟙 X) = p
    rw [Category.comp_id, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp])

/-- 概要：slice の反転と反転した図式の coslice の各次数の型は同値。
方針：錐を反転し、反転した標準単体の形状を標準同型で戻す。
規約：n は単体圏の対象。使われ方：slice の反転の同型の各成分。 -/
def sliceOverOpObjEquiv {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op.obj (Opposite.op n) ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.opFunctor.map p)).obj (Opposite.op n) :=
  (SSet.opObjEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) (n := Opposite.op n)).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseEquiv p (stdSimplex.obj n)).trans
      (cosliceDiagramReparamEquiv (SSet.opFunctor.map p) (stdSimplex.opIso n)))

/-- 概要：slice の反転の各次数の同値は標準単体と join の逆反転による前合成。
方針：図式の同値の順方向を計算して恒等射を消す。
規約：元の錐を表す射は opObjEquiv で取り出す。
使われ方：比較の単体作用と固定図式の計算。 -/
lemma sliceOverOpObjEquiv_val {K X : SSet.{u}} (p : K ⟶ X) (n : SimplexCategory)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op.obj (Opposite.op n)) :
    (sliceOverOpObjEquiv p n s).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso n).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (stdSimplex.obj n) K).inv ≫
          SSet.opFunctor.map (SSet.opObjEquiv s).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso n).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv (stdSimplex.obj n) K X (SSet.opObjEquiv s).val ≫ 𝟙 X.op = _
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneDiagramReverseHomEquiv_apply]

/-- 概要：slice の反転から反転図式の coslice への比較射。
方針：各次数の錐の反転の同値を、join の自然性と標準単体の逆反転の自然性で束ねる。
規約：値域は任意。使われ方：反転による極限と余極限の比較。 -/
def sliceOverOpMap {K X : SSet.{u}} (p : K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.opFunctor.map p) where
  app n := ↾(sliceOverOpObjEquiv p n.unop)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (sliceOverOpObjEquiv p ⦋m⦌ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op.map α s)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.map α.unop) ≫ (sliceOverOpObjEquiv p ⦋n⦌ s).val
    rw [sliceOverOpObjEquiv_val, sliceOverOpObjEquiv_val]
    have hs : (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op.map α s)).val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (SimplexCategory.rev.map α.unop)) (𝟙 K) ≫
          (SSet.opObjEquiv s).val := rfl
    rw [hs, SSet.opFunctor.map_comp]
    let V : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) K ⟶ X := (SSet.opObjEquiv s).val
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso ⦋m⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[m] K).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (SimplexCategory.rev.map α.unop)) (𝟙 K)) ≫
          SSet.opFunctor.map V =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.map α.unop) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso ⦋n⦌).inv ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] K).inv ≫ SSet.opFunctor.map V
    have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality
      (stdSimplex.map (SimplexCategory.rev.map α.unop)) (𝟙 K)
    simp only [CategoryTheory.Functor.map_id] at hR
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op)
      (SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α.unop))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] K).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[m] K).inv ≫
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (SimplexCategory.rev.map α.unop)) (𝟙 K)) at hR
    rw [← reassoc_of% hR]
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
    rw [stableStdSimplex_opIso_inv_naturality]

/-- 概要：slice の反転の比較射は同型。
方針：各次数の同値による全単射性を使う。
規約：追加の仮定なし。使われ方：slice／coslice の双対比較。 -/
instance sliceOverOpMap_isIso {K X : SSet.{u}} (p : K ⟶ X) : IsIso (sliceOverOpMap p) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).mpr (sliceOverOpObjEquiv p ⦋n⦌).bijective

/-- 概要：図式の slice の反転は、反転した図式の coslice と同型。
方針：錐の反転を全次数に自然な同値として束ねる。
規約：p と値域は任意。使われ方：S4 の引き戻しの貼り合わせへの双対化。 -/
def sliceOverOpIso {K X : SSet.{u}} (p : K ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.opFunctor.map p) := asIso (sliceOverOpMap p)

/-- 概要：標準単体からの射を反転しても Yoneda で表す単体は opObjEquiv による移送だけである。
方針：標準反転同型の逆が恒等単体を保つことを二重反転で計算する。
規約：標的は任意。使われ方：反転した slice の頂点射影。 -/
lemma stableReverseSimplex_yoneda {X : SSet.{u}} (n : SimplexCategory)
    (F : stdSimplex.obj n ⟶ X) :
    SSet.yonedaEquiv ((stdSimplex.opIso n).inv ≫ SSet.opFunctor.map F) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv F) := by
  obtain ⟨n⟩ := n
  rw [SSet.yonedaEquiv_comp, SSet.opFunctor_map]
  have hi : SSet.opObjEquiv (SSet.yonedaEquiv (stdSimplex.opIso.{u} ⦋n⦌).inv) =
      SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    change i.rev.rev = i
    exact Fin.rev_rev i
  rw [hi]
  rfl

/-- 概要：slice の反転同型は値域の反転への頂点射影と可換。
方針：右因子への制限を join の逆反転で左包含の op へ移し、Yoneda の反転の式を使う。
規約：射の厳密な等式。使われ方：反転した極限対象の頂点の一致。 -/
lemma sliceOverOpIso_projection {K X : SSet.{u}} (p : K ⟶ X) :
    (sliceOverOpIso p).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.opFunctor.map p) =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K.op Δ[n] ≫ (sliceOverOpObjEquiv p ⦋n⦌ s).val) = _
  rw [sliceOverOpObjEquiv_val]
  let V : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) K ⟶ X := (SSet.opObjEquiv s).val
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K.op Δ[n] ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso ⦋n⦌).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[n] K).inv ≫ SSet.opFunctor.map V)) =
    SSet.opObjEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] K ≫ V))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverse_inr_inv, ← SSet.opFunctor.map_comp]
  exact stableReverseSimplex_yoneda ⦋n⦌ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
