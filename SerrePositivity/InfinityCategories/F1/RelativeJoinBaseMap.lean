module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.F1.JoinDiagonalStdSimplex

/-!
概要：構造射の終域の変更による relative join の標準比較。
方針：左因子を保ち、右因子と底の円柱を終域の射で写して引き戻しへ持ち上げる。
規約：右因子は変更前と変更後の終域の恒等射。
使われ方：Kerodon Remark 5.2.3.9、Proposition 5.2.4.5 の終域の面への帰納。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終域への射を合成して得る relative join の標準射。
方針：通常の join と底の区間付き係数を同時に写す。
規約：左因子 X の係数は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5、終域を最後の面から広げる比較。 -/
noncomputable def relativeJoinBaseMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoin f (𝟙 Y) ⟶ relativeJoin (f ≫ h) (𝟙 Z) :=
  pullback.lift (pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ joinMap (𝟙 X) h)
    (pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ ((Δ[1] : SSet.{u}) ◁ h)) (by
      rw [Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id,
        Category.assoc, joinDiagonal_naturality, ← Category.assoc, ← pullback.condition,
        Category.assoc, ← joinMap_comp, Category.id_comp])

/-- 概要：終域の変更の射は通常の join への射影と可換。
方針：引き戻しの第一射影の計算則を使う。
規約：右の join の因子だけを h で写す。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の左因子の式。 -/
lemma relativeJoinBaseMap_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.fst (joinMap (f ≫ h) (𝟙 Z)) (joinDiagonal Z) =
      pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ joinMap (𝟙 X) h :=
  pullback.lift_fst _ _ _

/-- 概要：終域の変更の射は底の区間付き係数を h で写す。
方針：引き戻しの第二射影の計算則を使う。
規約：区間は恒等射で保つ。
使われ方：Kerodon Proposition 5.2.4.5、右錐の比較の底上の条件。 -/
lemma relativeJoinBaseMap_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    relativeJoinBaseMap f h ≫ pullback.snd (joinMap (f ≫ h) (𝟙 Z)) (joinDiagonal Z) =
      pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) ≫ ((Δ[1] : SSet.{u}) ◁ h) :=
  pullback.lift_snd _ _ _

/-- 概要：標準単体からの終域の単射に沿う relative join の比較は単射。
方針：元の第一射影と右因子の単射の join の合成の単射性を使う。
規約：変更前の終域が標準単体であることを要求する。
使われ方：Kerodon Proposition 5.2.4.5、最後の面に対応する部分複体の包含。 -/
instance relativeJoinBaseMap_stdSimplex_mono {X Z : SSet.{u}} {n : ℕ}
    (f : X ⟶ (Δ[n] : SSet.{u})) (h : (Δ[n] : SSet.{u}) ⟶ Z) [Mono h] :
    Mono (relativeJoinBaseMap f h) := by
  exact mono_of_mono_fac (relativeJoinBaseMap_fst f h)

end SerrePositivity.InfinityCategories
