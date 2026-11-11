module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedFatConeCurry

/-!
概要：fat join の左因子の時間と図式のホモトピーの時間を交換する円柱上の射。
方針：左因子の時間を取り出し、残りの三成分を元の fat join の円柱へ写す。
規約：join の区間とホモトピーの時間の二つの区間を区別する。
使われ方：Kerodon §4.6.6（Tag 04HY）、7.4.1.6（Tag 05QS） の両端固定のホモトピーの族への移送。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：時間付きの左因子の円柱を元の円柱と時間に分ける。
方針：直積の射影で成分を並べ替え、元の fat join の円柱の射を適用する。
規約：入力の順序は ((A×時間)×join の区間)×K。
使われ方：Kerodon §4.6.6（Tag 04HY） のホモトピーを族へ戻す円柱の入力。 -/
noncomputable def fatJoinTimeInput (A K : SSet.{u}) :
    ((A ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1]) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⊗ Δ[1] :=
  lift (lift (lift
    (fst ((A ⊗ Δ[1]) ⊗ Δ[1]) K ≫ fst (A ⊗ Δ[1]) Δ[1] ≫ fst A Δ[1])
    (fst ((A ⊗ Δ[1]) ⊗ Δ[1]) K ≫ snd (A ⊗ Δ[1]) Δ[1]))
    (snd ((A ⊗ Δ[1]) ⊗ Δ[1]) K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K)
    (fst ((A ⊗ Δ[1]) ⊗ Δ[1]) K ≫ fst (A ⊗ Δ[1]) Δ[1] ≫ snd A Δ[1])

/-- 概要：時間付き円柱の join の零端は左因子と時間に射影する。
方針：元の fat join の円柱の零端の式を各次数で評価する。
規約：時間は保持し、右因子だけを忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の貼り合わせの零端の整合性。 -/
lemma fatJoinTimeInput_zero (A K : SSet.{u}) :
    (SSet.ι₀ (X := A ⊗ (Δ[1] : SSet.{u})) ▷ K) ≫ fatJoinTimeInput A K =
      fst (A ⊗ (Δ[1] : SSet.{u})) K ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A K ▷ Δ[1]) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, k⟩
  have h := congrArg (fun f : A ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ↦ (f.app d (a, k), t))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero A K)
  exact h

/-- 概要：時間付き円柱の join の一端は右因子と時間に射影する。
方針：元の fat join の円柱の一端の式を各次数で評価する。
規約：左因子の A 成分だけを忘れる。
使われ方：Kerodon §4.6.6（Tag 04HY） の貼り合わせの一端の整合性。 -/
lemma fatJoinTimeInput_one (A K : SSet.{u}) :
    (SSet.ι₁ (X := A ⊗ (Δ[1] : SSet.{u})) ▷ K) ≫ fatJoinTimeInput A K =
      lift (snd (A ⊗ (Δ[1] : SSet.{u})) K)
        (fst (A ⊗ (Δ[1] : SSet.{u})) K ≫ snd A Δ[1]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ▷ Δ[1]) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, k⟩
  have h := congrArg (fun f : A ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ↦ (f.app d (a, k), t))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one A K)
  exact h

/-- 概要：時間の零端への制限は元の円柱の零時間への包含。
方針：直積の各成分を計算する。
規約：join の区間は変えない。
使われ方：Kerodon §4.6.6（Tag 04HY） の移送したホモトピーの始点。 -/
lemma fatJoinTimeInput_time_zero (A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (SSet.ι₀ (X := A)) (𝟙 K) ≫ fatJoinTimeInput A K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K ≫ SSet.ι₀ := rfl

/-- 概要：時間の一端への制限は元の円柱の一時間への包含。
方針：直積の各成分を計算する。
規約：join の区間は変えない。
使われ方：Kerodon §4.6.6（Tag 04HY） の移送したホモトピーの終点。 -/
lemma fatJoinTimeInput_time_one (A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (SSet.ι₁ (X := A)) (𝟙 K) ≫ fatJoinTimeInput A K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A K ≫ SSet.ι₁ := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
