module
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.SpectrumHomotopyFunctor

public import SerrePositivity.KST.Spectra.SpectrumHomotopyGroups
public import SerrePositivity.KST.Spectra.SpectrumMorphisms
public import Mathlib.Algebra.Category.Grp.Basic

/-!
概要：Ω スペクトルの整数次数のホモトピー群への関手。
方針：標準段での正次数の誘導準同型を使う。
規約：標準段 |j|+1 の計算次数の正値性を明示する。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の π_* 同型の界面。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：正次数の段の点つき射が誘導する群準同型。
方針：自然数次数を後者で場合分けし、KanHomotopyGroup.map を用いる。
規約：n>0 を明示する。
使われ方：BF 1978 §2、HA §1.4.2。整数次数の群への射の作用。 -/
def positiveLevelMap (X Y : OmegaSpectrum.{u}) (k n : ℕ) (hn : 0 < n)
    (f : (X.level k).space ⟶ (Y.level k).space) : levelHomotopy X k n →* levelHomotopy Y k n := by
  cases n with
  | zero => omega
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)

/-- 概要：段の正次数の準同型の元への作用は通常のホモトピー類の誘導写像。
方針：正次数の定義を展開する。
規約：n は実際の次数。
使われ方：BF 1978 §2。関手性の計算。 -/
theorem positiveLevelMap_apply (X Y : OmegaSpectrum.{u}) (k n : ℕ) (hn : 0 < n)
    (f : (X.level k).space ⟶ (Y.level k).space) (a : levelHomotopy X k n) :
    positiveLevelMap X Y k n hn f a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f) a := by
  cases n with
  | zero => omega
  | succ n => rfl

/-- 概要：スペクトルの射が整数次数のホモトピー群に誘導する準同型。
方針：標準段の正次数の射を取る。
規約：標準段は整数次数 j だけに依存する。
使われ方：BF 1978 §2、HA §1.4.2。定理 3.1 の π_* 同型。 -/
def homotopyMap {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    homotopyGroup X j →* homotopyGroup Y j :=
  positiveLevelMap X Y (canonicalLevel j) (degree j (canonicalLevel j)) (canonicalDegree_pos j)
    (f.app (canonicalLevel j))

/-- 概要：整数次数の誘導準同型を元の自然数次数の写像で計算する。
方針：正次数の段の写像の計算を適用する。
規約：標準段は |j|+1。
使われ方：BF 1978 §2。関手性と π_* 同型性の検査。 -/
@[simp]
theorem homotopyMap_apply {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ)
    (a : homotopyGroup X j) :
    homotopyMap f j a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (degree j (canonicalLevel j))
      (f.app (canonicalLevel j)).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a :=
  positiveLevelMap_apply _ _ _ _ _ _ _

/-- 概要：整数次数の誘導写像は恒等射を保つ。
方針：自然数次数の誘導写像の恒等法則を使う。
規約：群準同型の等式。
使われ方：BF 1978 §2、HA §1.4.2。π_j の関手。 -/
@[simp]
theorem homotopyMap_id (X : OmegaSpectrum.{u}) (j : ℤ) : homotopyMap (𝟙 X) j = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro a
  rw [homotopyMap_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id _ a

/-- 概要：整数次数の誘導写像は合成を保つ。
方針：自然数次数の誘導写像の合成法則を使う。
規約：準同型の合成の順序を保持する。
使われ方：BF 1978 §2、HA §1.4.2。π_j の関手。 -/
theorem homotopyMap_comp {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (j : ℤ) :
    homotopyMap (f ≫ g) j = (homotopyMap g j).comp (homotopyMap f j) := by
  apply MonoidHom.ext
  intro a
  rw [MonoidHom.comp_apply, homotopyMap_apply, homotopyMap_apply, homotopyMap_apply]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp _ _ _ _ _ _ a

/-- 概要：Ω スペクトルから整数次数の可換群への関手。
方針：構成済みの群と誘導準同型、恒等・合成法則を束ねる。
規約：可換群は乗法記法。必要に応じて Additive で加法化する。
使われ方：BF 1978 §2、HA §1.4.2。KST の全次数のホモトピー群。 -/
def homotopyFunctor (j : ℤ) : OmegaSpectrum.{u} ⥤ CommGrpCat.{u} where
  obj X := CommGrpCat.of (homotopyGroup X j)
  map f := CommGrpCat.ofHom (homotopyMap f j)
  map_id X := by exact congrArg CommGrpCat.ofHom (homotopyMap_id X j)
  map_comp f g := by exact congrArg CommGrpCat.ofHom (homotopyMap_comp f g j)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
