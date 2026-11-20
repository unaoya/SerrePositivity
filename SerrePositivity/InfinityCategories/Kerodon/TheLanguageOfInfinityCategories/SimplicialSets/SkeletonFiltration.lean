module


public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
概要：単体集合の骨格の関手性と、段に関する包含の自然性。
方針：次元 n 未満の非退化単体で生成される部分複体の像を比較する。
規約：Mathlib の skeleton n は次元 n 未満。通常の n 骨格には n+1 を使う。
使われ方：Goerss–Jardine VIII §1。部分 Tot の重みを作るための骨格の塔。

対応節は Kerodon 1.1（Tag 0004）。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletonFiltration
end SerrePositivity.KST.Spectra.SkeletonFiltration
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open _root_.SerrePositivity.KST.Spectra.SkeletonFiltration

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：射による骨格の像は標的の同じ段の骨格に入る。
方針：生成単体の像は元と同じ次元の単体から生成されることを使う。
規約：射は単射でなくてもよい。
使われ方：Goerss–Jardine VIII §1。骨格の制限射の構成。 -/
lemma image_le {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n).image f ≤ Y.skeleton n := by
  change (⨆ (i : Fin n) (x : X.nonDegenerate i), Subcomplex.ofSimplex x.1).image f ≤ _
  simp only [Subcomplex.image_iSup, iSup_le_iff, Subcomplex.image_ofSimplex]
  intro i x
  exact Y.ofSimplex_le_skeleton _ i.isLt

/-- 概要：単体集合の射を骨格へ制限する。
方針：部分複体からその像への射を骨格の包含へ後合成する。
規約：n は Mathlib の骨格の添字。
使われ方：Goerss–Jardine VIII §1。部分 Tot の重みの構造写像。 -/
def map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (X.skeleton n : SSet.{u}) ⟶ (Y.skeleton n : SSet.{u}) :=
  (X.skeleton n).toImage f ≫ Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.image_le f n)

@[reassoc (attr := simp)]
lemma map_ι {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map f n ≫ (Y.skeleton n).ι = (X.skeleton n).ι ≫ f := by
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map]

/-- 概要：固定した段の骨格は単体集合の関手となる。
方針：包含を後合成して恒等と合成の法則を検査する。
規約：骨格に Kan 性を要求しない。
使われ方：Goerss–Jardine VIII §1。標準単体の骨格の余単体図式。 -/
def functor (n : ℕ) : SSet.{u} ⥤ SSet.{u} where
  obj X := X.skeleton n
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map f n
  map_id X := by
    apply (cancel_mono (X.skeleton n).ι).1
    simp
  map_comp {X Y Z} f g := by
    apply (cancel_mono (Z.skeleton n).ι).1
    simp

/-- 概要：骨格から元の単体集合への包含は自然変換。
方針：制限射と包含の可換式を使う。
規約：n は固定する。
使われ方：Goerss–Jardine VIII §1。Tot から部分 Tot への比較射。 -/
def inclusion (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor.{u} n ⟶ 𝟭 SSet.{u} where
  app X := (X.skeleton n).ι
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.map_ι f n

/-- 概要：骨格の段の包含を自然変換に束ねる。
方針：元の単体集合への単射を後合成して自然性を検査する。
規約：n≤m の向きに重みが増加する。
使われ方：Goerss–Jardine VIII §1。部分 Tot の塔の遷移の重み。 -/
def transition {n m : ℕ} (h : n ≤ m) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor.{u} m where
  app X := Subcomplex.homOfLE (X.skeleton.monotone h)
  naturality X Y f := by
    apply (cancel_mono (Y.skeleton m).ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rfl

@[reassoc (attr := simp)]
lemma transition_inclusion {n m : ℕ} (h : n ≤ m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.transition.{u} h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion m = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.inclusion n := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
