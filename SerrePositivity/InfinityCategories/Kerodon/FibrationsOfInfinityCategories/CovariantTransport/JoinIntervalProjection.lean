module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection

/-!
概要：通常の join の左右の因子を区間の両端に送る射。
方針：両因子を点に写し、二点の join を標準区間へ移す。
規約：左側が時刻零、右側が時刻一。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、Proposition 5.2.3.15（Tag 024J）、ホーンの切断の計算。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：join の左右の頂点を区間の零・一に送る射。
方針：両因子の標準零単体への唯一の射の join を使う。
規約：因子は任意の単体集合。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、join のホーンを区間の値で分ける。 -/
def joinIntervalProjection (X Y : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y ⟶ (Δ[1] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.isTerminalObj₀.from X) (stdSimplex.isTerminalObj₀.from Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom

/-- 概要：区間へ写して二点の join に戻すと両因子の点への射が得られる。
方針：標準同型の順・逆を打ち消す。
規約：係数を忘れた後も切断は保つ。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、区間の逆像と join の切断の整合性。 -/
lemma joinIntervalProjection_intervalJoin (X Y : SSet.{u}) :
    joinIntervalProjection X Y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.isTerminalObj₀.from X) (stdSimplex.isTerminalObj₀.from Y) := by
  rw [joinIntervalProjection, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：join の単体の切断は区間の零の逆像の頂点数と一致する。
方針：区間を二点の join に戻す公式を単体の切断に適用する。
規約：n は単体の次数。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの切断の分類。 -/
lemma joinIntervalProjection_app_cut (X Y : SSet.{u}) (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv
      ((joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s)).toOrderHom 1 = s.1.val := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalJoin_cut]
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋n⦌) s) (joinIntervalProjection_intervalJoin X Y)
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) Δ[0] n ↦ t.1.val) he

/-- 概要：join の単体の頂点は切断より左なら、かつそのときに限り時刻零に写る。
方針：区間の零の逆像と切断の等式を各頂点で読む。
規約：頂点番号 j は零から数える。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、ホーンの左右の部分の判定。 -/
lemma joinIntervalProjection_app_eq_zero_iff (X Y : SSet.{u}) (n : ℕ)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join X Y) _⦋n⦌) (j : Fin (n + 1)) :
    (joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s j = 0 ↔ j.val < s.1.val := by
  let t := (joinIntervalProjection X Y).app (Opposite.op ⦋n⦌) s
  have hc := joinIntervalProjection_app_cut X Y n s
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 j
  change j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 ↔ (t j).val < 1 at hh
  rw [hc] at hh
  constructor
  · intro hz
    apply hh.mpr
    rw [show t j = 0 from hz]
    decide
  · intro hj
    apply Fin.ext
    have ht := hh.mp hj
    change (t j).val < 1 at ht
    change (t j).val = 0
    omega

/-- 概要：join の区間への射影は左右の因子の射に自然。
方針：joinMap の合成則と零単体への射の一意性を使う。
規約：両因子の射は独立に指定する。
使われ方：Kerodon Lemma 5.2.3.13（Tag 02RF）、相対 join の内ホーンの底変換。 -/
lemma joinIntervalProjection_naturality {X Y X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g ≫ joinIntervalProjection X' Y' = joinIntervalProjection X Y := by
  rw [joinIntervalProjection, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  rw [show f ≫ stdSimplex.isTerminalObj₀.from X' = stdSimplex.isTerminalObj₀.from X from
    stdSimplex.isTerminalObj₀.hom_ext _ _]
  rw [show g ≫ stdSimplex.isTerminalObj₀.from Y' = stdSimplex.isTerminalObj₀.from Y from
    stdSimplex.isTerminalObj₀.hom_ext _ _]
  rfl

/-- 概要：区間付き対角の後で join の区間へ射影すると元の区間成分になる。
方針：切断の計算から各頂点の時刻零の判定が一致することを使う。
規約：係数 K の充填性は要求しない。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、対角に沿う内ホーンの底の一致。 -/
lemma joinDiagonal_joinIntervalProjection (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal K ≫ joinIntervalProjection K K = fst (Δ[1] : SSet.{u}) K := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  apply stdSimplex.ext
  intro j
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal K).app (Opposite.op ⦋n⦌) (t, a)
  let b := (joinIntervalProjection K K).app (Opposite.op ⦋n⦌) z
  have hz : b j = 0 ↔ t j = 0 := by
    rw [joinIntervalProjection_app_eq_zero_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_app_cut]
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 j
    constructor
    · intro hj
      apply Fin.ext
      have ht := hh.mp hj
      change (t j).val < 1 at ht
      change (t j).val = 0
      omega
    · intro ht
      apply hh.mpr
      change (t j).val < 1
      rw [ht]
      decide
  apply Fin.ext
  change (b j).val = (t j).val
  have hz' : (b j).val = 0 ↔ (t j).val = 0 := by
    simpa only [Fin.ext_iff, Fin.val_zero] using hz
  have hb := (b j).isLt
  have ht := (t j).isLt
  omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
