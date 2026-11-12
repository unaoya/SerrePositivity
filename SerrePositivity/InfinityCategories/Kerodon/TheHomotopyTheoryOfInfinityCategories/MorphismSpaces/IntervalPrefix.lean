module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMinimum
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：矢印を始点から少しずつ伸ばす正方形の時間写像。
方針：二つの区間の最小値を取り、一方の時刻を固定して四辺を読む。
規約：外側の時間が伸長、内側の時間が矢印の区間。
使われ方：B1 の coherent な矢印比較を抽出した単位の合成と照合する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：パラメータを保ち二つの時刻を最小値でまとめる。
方針：結合子の後に区間の最小値を作用させる。
規約：始域は (A×Δ[1])×Δ[1]。
使われ方：ホモトピーの伸長を表す raw な射。 -/
def intervalPrefixTime (A : SSet.{u}) : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ A ⊗ Δ[1] :=
  (α_ A (Δ[1] : SSet.{u}) Δ[1]).hom ≫ (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum)

/-- 概要：内側の時刻零では元の矢印の始点。
方針：最小値 min(t,0)=0 を各頂点で計算する。
規約：厳密な射の等式。使われ方：伸長中の始域固定。 -/
lemma intervalPrefixTime_arrow_zero (A : SSet.{u}) :
    SSet.ι₀ ≫ intervalPrefixTime A = fst A (Δ[1] : SSet.{u}) ≫ SSet.ι₀ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    change min (z.2 i) 0 = 0
    exact min_eq_right (Fin.zero_le _)

/-- 概要：内側の時刻一では伸長の時刻そのもの。
方針：最小値 min(t,1)=t を各頂点で計算する。
規約：厳密な射の等式。使われ方：伸長中の標的の回収。 -/
lemma intervalPrefixTime_arrow_one (A : SSet.{u}) :
    SSet.ι₁ ≫ intervalPrefixTime A = 𝟙 (A ⊗ Δ[1]) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    change min (z.2 i) 1 = z.2 i
    exact min_eq_left (Fin.le_last _)

/-- 概要：伸長の時刻零では元の始点に留まる。
方針：最小値 min(0,s)=0 を各頂点で計算する。
規約：厳密な射の等式。使われ方：恒等矢印の族の回収。 -/
lemma intervalPrefixTime_start (A : SSet.{u}) :
    ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫ intervalPrefixTime A =
      fst A (Δ[1] : SSet.{u}) ≫ SSet.ι₀ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    change min 0 (z.2 i) = 0
    exact min_eq_left (Fin.zero_le _)

/-- 概要：伸長の時刻一では元の矢印を回収する。
方針：最小値 min(1,s)=s を各頂点で計算する。
規約：厳密な射の等式。使われ方：比較に入れた矢印の族の回収。 -/
lemma intervalPrefixTime_end (A : SSet.{u}) :
    ((SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫ intervalPrefixTime A =
      𝟙 (A ⊗ Δ[1]) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro i
    change min 1 (z.2 i) = z.2 i
    exact min_eq_right (Fin.le_last _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
