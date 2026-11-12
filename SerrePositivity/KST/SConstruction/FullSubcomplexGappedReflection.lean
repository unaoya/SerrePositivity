module
public import SerrePositivity.KST.SConstruction.FullSubcomplexColimits
public import SerrePositivity.KST.SConstruction.Gapped

/-! # 全部分複体による gapped 条件の反映
概要：周囲で零対角と押し出しを持つ全部分複体値の Ar 図式は、内部でも gapped。
方針：零対象と余極限錐の普遍性を全部分複体へ反映する。
規約：周囲だけ quasicategory。使われ方：cofiber 図式交換の逆向き。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全部分複体への四角形の周囲での押し出し性を内部へ反映する。 -/
lemma isPushoutSquare_fullSubcomplex_of_ambient {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop)
    (G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}))
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (G ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G := by
  apply isColimitCone_fullSubcomplex_of_ambient P (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone G)
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ (Category.assoc _ _ _)).2 hG

/-- 全部分複体値の Ar 図式の gapped 性を周囲から反映する。 -/
lemma IsGapped.of_fullSubcomplex {n : ℕ} {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) {F : arNerve n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})}
    (hF : IsGapped (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)) : IsGapped F := by
  constructor
  · intro i
    exact ⟨isInitialVertex_fullSubcomplex_of_ambient P _ (hF.1 i).1,
      isTerminalVertex_fullSubcomplex_of_ambient P _ (hF.1 i).2⟩
  · intro i j k l hij hjk hkl
    apply isPushoutSquare_fullSubcomplex_of_ambient P
    simpa only [Category.assoc] using hF.2 i j k l hij hjk hkl

end SerrePositivity.KST.SConstruction
