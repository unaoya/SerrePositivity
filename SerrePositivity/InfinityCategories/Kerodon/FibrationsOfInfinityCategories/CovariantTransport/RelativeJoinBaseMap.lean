module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonalStdSimplex

/-!
概要：構造射の終域の変更による relative join の標準比較。
方針：左因子を保ち、右因子と底の円柱を終域の射で写して引き戻しへ持ち上げる。
規約：右因子は変更前と変更後の終域の恒等射。
使われ方：Kerodon Remark 5.2.3.9（Tag 024A）、Proposition 5.2.4.5（Tag 024R） の終域の面への帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：終域への射を合成して得る relative join の標準射。
方針：通常の join と底の区間付き係数を同時に写す。
規約：左因子 X の係数は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域を最後の面から広げる比較。 -/
noncomputable def relativeJoinBaseMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (f ≫ h) (𝟙 Z) :=
  pullback.lift (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 X) h)
    (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) ≫ ((Δ[1] : SSet.{u}) ◁ h)) (by
      rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality, ← Category.assoc, ← pullback.condition,
        Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp])

/-- 概要：終域の変更の射は通常の join への射影と可換。
方針：引き戻しの第一射影の計算則を使う。
規約：右の join の因子だけを h で写す。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の左因子の式。 -/
lemma relativeJoinBaseMap_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ≫ h) (𝟙 Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Z) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 X) h :=
  pullback.lift_fst _ _ _

/-- 概要：終域の変更の射は底の区間付き係数を h で写す。
方針：引き戻しの第二射影の計算則を使う。
規約：区間は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、右錐の比較の底上の条件。 -/
lemma relativeJoinBaseMap_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (f ≫ h) (𝟙 Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Z) =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Y) ≫ ((Δ[1] : SSet.{u}) ◁ h) :=
  pullback.lift_snd _ _ _

/-- 概要：標準単体からの終域の単射に沿う relative join の比較は単射。
方針：元の第一射影と右因子の単射の join の合成の単射性を使う。
規約：変更前の終域が標準単体であることを要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の面に対応する部分複体の包含。 -/
instance relativeJoinBaseMap_stdSimplex_mono {X Z : SSet.{u}} {n : ℕ}
    (f : X ⟶ (Δ[n] : SSet.{u})) (h : (Δ[n] : SSet.{u}) ⟶ Z) [Mono h] :
    Mono (relativeJoinBaseMap f h) := by
  exact mono_of_mono_fac (relativeJoinBaseMap_fst f h)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
