module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordLength
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# 全語の図式の長さを制限した余極限

概要：元の語の図式を長さで制限した段階と、上限を増やす元の標準比較を構成する。
方針：同じ固定語の標準射で余錐を定め、元の余極限の普遍性を適用する。
規約：図式の proper 性は不要。段階が単射であることはまだ主張しない。
使われ方：全語の余極限の Nat に沿った濾過。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w})

def lengthStage (n : ℕ) : SSet.{w} := colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F)

def lengthStageInclusion (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    F.obj a ⟶ lengthStage F n := colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F) ⟨a, ha⟩

lemma lengthStageInclusion_naturality (n : ℕ) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (ha : a.length ≤ n) (hb : b.length ≤ n) (f : a ⟶ b) :
    F.map f ≫ lengthStageInclusion F n b hb = lengthStageInclusion F n a ha :=
  colimit.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F) (ObjectProperty.homMk f :
    (⟨a, ha⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n) ⟶ ⟨b, hb⟩)

def lengthStageTransition {n m : ℕ} (h : n ≤ m) : lengthStage F n ⟶ lengthStage F m :=
  colimit.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthInclusion n ⋙ F)
    { pt := lengthStage F m
      ι :=
        { app a := lengthStageInclusion F m a.obj (a.property.trans h)
          naturality a b f := by
            change F.map f.hom ≫ lengthStageInclusion F m b.obj (b.property.trans h) =
              lengthStageInclusion F m a.obj (a.property.trans h) ≫ 𝟙 _
            rw [Category.comp_id]
            exact lengthStageInclusion_naturality F m (a.property.trans h)
              (b.property.trans h) f.hom } }

lemma lengthStageInclusion_transition {n m : ℕ} (h : n ≤ m) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (ha : a.length ≤ n) :
    lengthStageInclusion F n a ha ≫ lengthStageTransition F h =
      lengthStageInclusion F m a (ha.trans h) := colimit.ι_desc _ _

lemma lengthStageTransition_refl (n : ℕ) : lengthStageTransition F (le_refl n) = 𝟙 _ := by
  apply colimit.hom_ext
  intro a
  change lengthStageInclusion F n a.obj a.property ≫ lengthStageTransition F _ =
    lengthStageInclusion F n a.obj a.property ≫ 𝟙 _
  rw [lengthStageInclusion_transition, Category.comp_id]

lemma lengthStageTransition_comp {n m l : ℕ} (h : n ≤ m) (h' : m ≤ l) :
    lengthStageTransition F h ≫ lengthStageTransition F h' =
      lengthStageTransition F (h.trans h') := by
  apply colimit.hom_ext
  intro a
  change lengthStageInclusion F n a.obj a.property ≫
    (lengthStageTransition F h ≫ lengthStageTransition F h') =
    lengthStageInclusion F n a.obj a.property ≫ lengthStageTransition F (h.trans h')
  rw [← Category.assoc, lengthStageInclusion_transition, lengthStageInclusion_transition,
    lengthStageInclusion_transition]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
