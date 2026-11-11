module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxSlice

/-!
概要：太い slice の普遍族を左因子と円柱上で評価する入力。
方針：零単体の唯一の値と元のパラメーターを直積へ並べる。
規約：区間の座標と右因子を保持する。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い join の uncurry。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：太い零単体の左端とパラメーターからなる入力。
方針：零単体への唯一の射を左端へ含める。
規約：パラメーターを第二因子に保持する。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い join の左成分の評価。 -/
noncomputable def laxSliceLeftInput (A K : SSet.{u}) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ⊗ A :=
  lift (stdSimplex.isTerminalObj₀.from A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K) (𝟙 A)

/-- 概要：太い join の円柱を太い零単体の円柱とパラメーターに分ける入力。
方針：元の左成分をパラメーターへ、区間と右成分を円柱へ送る。
規約：零単体の値は唯一の射で指定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い join の円柱成分の評価。 -/
noncomputable def laxSliceCylinderInput (A K : SSet.{u}) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ⊗ A :=
  lift (lift (lift (stdSimplex.isTerminalObj₀.from _)
      (fst (A ⊗ Δ[1]) K ≫ snd A Δ[1])) (snd (A ⊗ Δ[1]) K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] K)
    (fst (A ⊗ Δ[1]) K ≫ fst A Δ[1])

/-- 概要：円柱の零端の入力は左成分の入力に射影する。
方針：太い円柱の零端の潰しと直積の成分を計算する。
規約：右成分を忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い join の貼り合わせの零端。 -/
lemma laxSliceCylinderInput_zero (A K : SSet.{u}) :
    (SSet.ι₀ (X := A) ▷ K) ≫ laxSliceCylinderInput A K = fst A K ≫ laxSliceLeftInput A K := by
  have ht : (SSet.ι₀ (X := A) ▷ K) ≫
      lift (lift (stdSimplex.isTerminalObj₀.from _)
        (fst (A ⊗ Δ[1]) K ≫ snd A Δ[1])) (snd (A ⊗ Δ[1]) K) =
      lift (stdSimplex.isTerminalObj₀.from (A ⊗ K) ≫ SSet.ι₀) (snd A K) := by
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      · rfl
    · rfl
  rw [laxSliceCylinderInput, comp_lift, ← Category.assoc, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero]
  apply CartesianMonoidalCategory.hom_ext
  · change stdSimplex.isTerminalObj₀.from (A ⊗ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K =
      fst A K ≫ stdSimplex.isTerminalObj₀.from A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] K
    rw [← Category.assoc]
    congr 1
  · rfl

/-- 概要：円柱の一端の入力は右包含とパラメーターに射影する。
方針：太い円柱の一端の潰しと直積の成分を計算する。
規約：左成分はパラメーターにのみ残す。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い join の貼り合わせの一端。 -/
lemma laxSliceCylinderInput_one (A K : SSet.{u}) :
    (SSet.ι₁ (X := A) ▷ K) ≫ laxSliceCylinderInput A K =
      (β_ A K).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) := by
  have ht : (SSet.ι₁ (X := A) ▷ K) ≫
      lift (lift (stdSimplex.isTerminalObj₀.from _)
        (fst (A ⊗ Δ[1]) K ≫ snd A Δ[1])) (snd (A ⊗ Δ[1]) K) =
      lift (stdSimplex.isTerminalObj₀.from (A ⊗ K) ≫ SSet.ι₁) (snd A K) := by
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      · rfl
    · rfl
  rw [laxSliceCylinderInput, comp_lift, ← Category.assoc, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
