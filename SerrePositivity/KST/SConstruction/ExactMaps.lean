module
public import SerrePositivity.KST.SConstruction.FirstRowFibration

/-! # S 構成が必要とする射の保存条件
概要：零頂点と押し出し正方形を保つ射は gapped 図式を保つ。
方針：gapped の二つの頂点条件を後合成で移す。
規約：本レーンの保存条件であり、α-S の安定性の定義は変更しない。
使われ方：BGT §7 の S 構成の関手性と反復。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：S 構成に必要な零対象と押し出しの保存条件。
方針：頂点と実際の正方形の普遍性をそれぞれ量化する。
規約：h 圏の押し出しに置き換えない。使われ方：gapped 図式の後合成。 -/
def PreservesSConstructionData {C D : SSet.{u}} (f : C ⟶ D) : Prop :=
  (∀ z : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (f.app (Opposite.op ⦋0⦌) z)) ∧
    (∀ F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ f))

/-- 概要：恒等射は S 構成の保存条件を満たす。
方針：零頂点と正方形を変えないことを使う。
規約：quasicategory 性は不要。使われ方：後合成の恒等法則。 -/
lemma preservesSConstructionData_id (C : SSet.{u}) : PreservesSConstructionData (𝟙 C) := by
  constructor
  · intro z hz
    exact hz
  · intro F hF
    simpa only [Category.comp_id] using hF

/-- 概要：S 構成の保存条件は射の合成で閉じる。
方針：零頂点と押し出しの保存を二回適用する。
規約：quasicategory 性は不要。使われ方：後合成の合成法則。 -/
lemma PreservesSConstructionData.comp {C D E : SSet.{u}} {f : C ⟶ D} {g : D ⟶ E}
    (hf : PreservesSConstructionData f) (hg : PreservesSConstructionData g) :
    PreservesSConstructionData (f ≫ g) := by
  constructor
  · intro z hz
    exact hg.1 _ (hf.1 z hz)
  · intro F hF
    simpa only [Category.assoc] using hg.2 (F ≫ f) (hf.2 F hF)

/-- 概要：零対象と押し出しを保つ射による後合成は gapped 図式を保つ。
方針：零対角を頂点で、全正方形の普遍性を後合成で確認する。
規約：全弱不等式の正方形を含む。使われ方：S_n の後合成写像。 -/
lemma IsGapped.postcomp {n : ℕ} {C D : SSet.{u}} {F : arNerve n ⟶ C}
    (hF : IsGapped F) (f : C ⟶ D) (hf : PreservesSConstructionData f) : IsGapped (F ≫ f) := by
  constructor
  · intro i
    exact hf.1 _ (hF.1 i)
  · intro i j k l hij hjk hkl
    rw [← Category.assoc]
    exact hf.2 _ (hF.2 i j k l hij hjk hkl)

end SerrePositivity.KST.SConstruction
