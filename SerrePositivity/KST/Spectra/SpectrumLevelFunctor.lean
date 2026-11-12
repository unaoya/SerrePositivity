module

public import SerrePositivity.KST.Spectra.OmegaTransitionNaturality

/-!
概要：Ω スペクトルの各段の全自然数次数の可換群への関手。
方針：零次数では次段の一次へ移した群構造と隣接比較の自然性を使う。
規約：順写像は元の KanHomotopy.map そのもの。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の任意段表示の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：スペクトルの射は各段の零次数を含む可換群の準同型を誘導する。
方針：正次数は既存の準同型、零次数は隣接段の一次への群同型とその自然性を使う。
規約：順写像は構成済みのホモトピー類の写像を保持する。
使われ方：BF 1978 §2、HA §1.4.2。全自然数次数の段の関手性。 -/
def levelMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (k n : ℕ) :
    levelHomotopy X k n →* levelHomotopy Y k n where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
  map_one' := by
    rw [← levelPoint_eq_one X k n, ← levelPoint_eq_one Y k n]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_point n (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
  map_mul' := by
    intro a b
    cases n with
    | zero =>
      apply (transition Y k 0).injective
      rw [transition_natural f k 0, (transition Y k 0).map_mul,
        transition_natural f k 0, transition_natural f k 0, (transition X k 0).map_mul]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := 0) (f.app (k + 1)).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)).map_mul _ _
    | succ n =>
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)).map_mul a b

/-- 概要：段の準同型の順写像は通常のホモトピー類の誘導写像。
方針：構成の定義を読む。
規約：零次数も含む。
使われ方：BF 1978 §2。段の比較の自然性の計算。 -/
@[simp]
theorem levelMap_apply {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (k n : ℕ)
    (a : levelHomotopy X k n) :
    levelMap f k n a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a := rfl

/-- 概要：各段の誘導準同型は恒等射を保つ。
方針：ホモトピー類の恒等法則を使う。
規約：全自然数次数。
使われ方：BF 1978 §2。段の可換群への関手。 -/
@[simp]
theorem levelMap_id (X : OmegaSpectrum.{u}) (k n : ℕ) : levelMap (𝟙 X) k n = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id n a

/-- 概要：各段の誘導準同型は合成を保つ。
方針：ホモトピー類の合成法則を使う。
規約：全自然数次数。
使われ方：BF 1978 §2。段の可換群への関手。 -/
theorem levelMap_comp {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k n : ℕ) :
    levelMap (f ≫ g) k n = (levelMap g k n).comp (levelMap f k n) := by
  apply MonoidHom.ext
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n (f.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _)
    (g.app k).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (f.app k ≫ g.app k)) a

/-- 概要：指定段・指定次数の可換群への関手。
方針：全次数の誘導準同型と恒等・合成法則を束ねる。
規約：零次数の群構造は Ω 条件によって次段から移したもの。
使われ方：BF 1978 §2、HA §1.4.2。任意段でのホモトピー群の計算。 -/
def levelFunctor (k n : ℕ) : OmegaSpectrum.{u} ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (levelHomotopy X k n)
  map f := CommGrpCat.ofHom (levelMap f k n)
  map_id X := congrArg CommGrpCat.ofHom (levelMap_id X k n)
  map_comp f g := congrArg CommGrpCat.ofHom (levelMap_comp f g k n)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
