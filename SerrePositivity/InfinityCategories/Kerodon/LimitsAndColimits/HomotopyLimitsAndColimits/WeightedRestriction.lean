module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections

/-!
概要：重みの自然変換による重み付き end の反変な制限。
方針：パラメーター付き自然変換の重みの変数に前合成し、end の普遍性へ戻す。
規約：図式 H は固定する。比較は実際の前合成の射。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5） の homotopy 極限模型の重みの比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：重みの自然変換による切断空間の反変な射。
方針：普遍的なパラメーター付き自然変換の重みの変数に前合成する。
規約：j : W → W' から end(W',H) → end(W,H) の向き。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の標準比較と重みの置換。 -/
noncomputable def weightedSectionsPre {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    (H : I ⥤ SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift
    ((j ▷ (Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H)))

/-- 概要：重みの制限の各成分は内部 Hom の前合成。
方針：end の射影と curry の前合成の公式を使う。
規約：重みの射 j の実際の成分を使う。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の重みの比較射の成分の計算。 -/
lemma weightedSectionsPre_π {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    (H : I ⥤ SSet.{u}) (i : I) :
    weightedSectionsPre j H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W' H i ≫ (pre (j.app i)).app (H.obj i) := by
  rw [weightedSectionsPre, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  change curry ((j.app i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H) ≫
    uncurry (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W' H i)) = _
  rw [← curry_pre_app, curry_uncurry, Category.id_comp]

/-- 概要：重みの制限は任意のパラメーター付き自然変換への前合成と一致する。
方針：各成分で uncurry と内部 Hom の前合成の交換を使う。
規約：パラメーター X の Kan 性は不要。
使われ方：Kerodon 7.5.3（Tag 03AP）、重みの比較の相対的な充填。 -/
lemma weightedSectionsUncurry_comp_pre {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    {H : I ⥤ SSet.{u}} {X : SSet.{u}} (f : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W' H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (f ≫ weightedSectionsPre j H) =
      (j ▷ (Functor.const I).obj X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry f := by
  apply NatTrans.ext
  funext i
  change uncurry ((f ≫ weightedSectionsPre j H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H i) =
    (j.app i ▷ X) ≫ uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W' H i)
  rw [Category.assoc, weightedSectionsPre_π, ← Category.assoc, uncurry_pre_app]

/-- 概要：重みの恒等射による制限は恒等射。
方針：全ての内部 Hom への射影で前合成の恒等則を使う。
規約：Kan 性を仮定しない。
使われ方：Kerodon 7.5.3（Tag 03AP） の重みの比較の関手則。 -/
lemma weightedSectionsPre_id (W H : I ⥤ SSet.{u}) :
    weightedSectionsPre (𝟙 W) H = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [weightedSectionsPre_π]
  simp

/-- 概要：重みの合成の制限は反対順の制限の合成。
方針：全ての内部 Hom への射影で前合成の合成則を使う。
規約：重みに関して反変な向き。
使われ方：Kerodon 7.5.3（Tag 03AP） の複数の重みの比較。 -/
lemma weightedSectionsPre_comp {W W' W'' : I ⥤ SSet.{u}}
    (j : W ⟶ W') (k : W' ⟶ W'') (H : I ⥤ SSet.{u}) :
    weightedSectionsPre (j ≫ k) H = weightedSectionsPre k H ≫ weightedSectionsPre j H := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [weightedSectionsPre_π, Category.assoc, weightedSectionsPre_π,
    ← Category.assoc, weightedSectionsPre_π]
  simp only [NatTrans.comp_app, pre_map, Category.assoc]

/-- 概要：strict な錐の標準比較は重みの制限に整合する。
方針：各成分で、重みを忘れる第二射影と重みの前合成の可換性を使う。
規約：選択した逆射ではなく、実際の weightedConeComparison の等式。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の κ と補助的な重み付き模型との整合性。 -/
lemma weightedConeComparison_pre {W W' : I ⥤ SSet.{u}} (j : W ⟶ W')
    {H : I ⥤ SSet.{u}} (c : CategoryTheory.Limits.Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W' c ≫ weightedSectionsPre j H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro i
  rw [Category.assoc, weightedSectionsPre_π, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π, curry_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
  apply congrArg curry
  rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_snd]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
