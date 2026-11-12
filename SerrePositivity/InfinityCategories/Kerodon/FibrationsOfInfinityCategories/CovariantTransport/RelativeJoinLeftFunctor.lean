module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoin
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：共通の底と右因子を固定した relative join の左因子に関する関手性。
方針：通常の join の誘導射を引き戻しへ持ち上げ、その両射影で関手の法則を示す。
規約：始域は通常の圏 Over S、値域は単体集合の圏。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域のセル分解に沿った比較の貼り合わせ。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：底を保つ左因子の射が relative join の射を誘導する。
方針：通常の join の左因子を写し、区間付きの底は保ったまま引き戻しへ持ち上げる。
規約：h は左因子の射が共通の底を保つ等式。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの包含による relative join の比較。 -/
noncomputable def relativeJoinLeftMap {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f' g :=
  pullback.lift (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u (𝟙 Y))
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) (by
      rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, h, Category.id_comp, pullback.condition])

/-- 概要：relative join の左因子の誘導射は通常の join への第一射影と可換。
方針：引き戻しの持ち上げの第一射影の式を使う。
規約：右因子は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join の比較の通常の join への射影。 -/
lemma relativeJoinLeftMap_fst {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    relativeJoinLeftMap g u h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u (𝟙 Y) :=
  pullback.lift_fst _ _ _

/-- 概要：relative join の左因子の誘導射は区間付きの底への第二射影を保つ。
方針：引き戻しの持ち上げの第二射影の式を使う。
規約：共通の底 S は固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、同じ底の上の誘導射の計算。 -/
lemma relativeJoinLeftMap_snd {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    relativeJoinLeftMap g u h ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) := pullback.lift_snd _ _ _

/-- 概要：relative join の左因子の恒等射は全空間の恒等射になる。
方針：引き戻しの両射影で通常の join の恒等則を使う。
規約：底上の可換性の証明の選択は問わない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、relative join 関手の単位則。 -/
lemma relativeJoinLeftMap_id {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : 𝟙 X ≫ f = f) : relativeJoinLeftMap g (𝟙 X) h = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f g) := by
  apply pullback.hom_ext
  · rw [relativeJoinLeftMap_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.comp_id, Category.id_comp]
  · rw [relativeJoinLeftMap_snd, Category.id_comp]

/-- 概要：relative join の左因子の誘導射は合成を保つ。
方針：引き戻しの両射影で通常の join の合成則と第二射影の保存を使う。
規約：h' は合成が底を保つ任意の証明。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの包含の合成への作用。 -/
lemma relativeJoinLeftMap_comp {X X' X'' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} {f'' : X'' ⟶ S}
    (u : X ⟶ X') (v : X' ⟶ X'') (hu : u ≫ f' = f) (hv : v ≫ f'' = f')
    (h' : (u ≫ v) ≫ f'' = f) :
    relativeJoinLeftMap g (u ≫ v) h' = relativeJoinLeftMap g u hu ≫ relativeJoinLeftMap g v hv := by
  apply pullback.hom_ext
  · rw [relativeJoinLeftMap_fst, Category.assoc, relativeJoinLeftMap_fst,
      ← Category.assoc, relativeJoinLeftMap_fst, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  · rw [relativeJoinLeftMap_snd, Category.assoc, relativeJoinLeftMap_snd, relativeJoinLeftMap_snd]

/-- 概要：右因子と共通の底を固定した relative join の関手。
方針：Over S の対象の構造射を左因子に使い、底を保つ射の誘導射を束縛する。
規約：通常の圏の関手であり、空間の ∞ 余極限の存在を主張しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域のセル分解による自然な比較の貼り合わせ。 -/
noncomputable def relativeJoinLeftFunctor {Y S : SSet.{u}} (g : Y ⟶ S) :
    Over S ⥤ SSet.{u} where
  obj f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f.hom g
  map u := relativeJoinLeftMap g u.left u.w
  map_id f := relativeJoinLeftMap_id f.hom g _
  map_comp u v := relativeJoinLeftMap_comp g u.left v.left u.w v.w _

/-- 概要：左因子の relative join の誘導射と通常の join の射の比較四角形は pullback。
方針：同じ区間付き対角への二つの引き戻しを横に貼り、右の引き戻しを取り消す。
規約：左因子の射の単射性は不要。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、join の pushout から relative join の pushout への移行。 -/
lemma relativeJoinLeftMap_isPullback {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') (h : u ≫ f' = f) :
    IsPullback (relativeJoinLeftMap g u h)
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u (𝟙 Y)) := by
  have hp : IsPullback
      (relativeJoinLeftMap g u h ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u (𝟙 Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) := by
    simpa only [relativeJoinLeftMap_snd, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, h, Category.id_comp] using
      (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)).flip
  exact hp.of_right (relativeJoinLeftMap_fst g u h)
    (IsPullback.of_hasPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f' g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)).flip

/-- 概要：左因子の単射は relative join の単射を誘導する。
方針：通常の join の単射保存を比較の pullback 四角形へ移す。
規約：底や右因子の射には単射性を仮定しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルの貼り合わせの単射条件。 -/
instance relativeJoinLeftMap_mono {X X' Y S : SSet.{u}} (g : Y ⟶ S)
    {f : X ⟶ S} {f' : X' ⟶ S} (u : X ⟶ X') [Mono u] (h : u ≫ f' = f) :
    Mono (relativeJoinLeftMap g u h) := (relativeJoinLeftMap_isPullback g u h).mono_fst_of_mono

/-- 概要：relative join の左因子の関手は単射を保つ。
方針：Over の単射の左成分の単射性を、relative join の誘導射の単射性へ移す。
規約：共通の底と右因子は固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セル分解に沿う自然な比較の貼り合わせ。 -/
instance relativeJoinLeftFunctor_preservesMonomorphisms {Y S : SSet.{u}} (g : Y ⟶ S) :
    (relativeJoinLeftFunctor g).PreservesMonomorphisms where
  preserves u _ := relativeJoinLeftMap_mono g u.left u.w

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
