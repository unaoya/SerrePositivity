module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinLeftMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjointPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.TensorExchangePullback

/-!
概要：fat join の右因子の単射の保存。
方針：零端の貼り合わせの外にある一端の逆像を計算し、第二の pushout を比較する。
規約：左因子は任意、quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の右因子のセル分解。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の最初の pushout に右因子の射を作用させる。
方針：円柱と零端の写像を貼り合わせる。
規約：固定する左因子は K。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然性の正方形。 -/
noncomputable def fatJoinStageMapRight {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage K A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage K B :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 K) f ≫ pushout.inl _ _) (pushout.inr _ _)
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap_zero, Category.assoc,
      pushout.condition, ← Category.assoc, tensorHom_fst, Category.comp_id])

/-- 概要：最初の pushout の右因子の誘導射の円柱上の制限。
方針：pushout の desc の計算。
規約：左包含は円柱からの射。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然性。 -/
lemma fatJoinStageMapRight_inl {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) :
    pushout.inl (SSet.ι₀ (X := K) ▷ A) (fst K A) ≫ fatJoinStageMapRight K f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 K) f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _

/-- 概要：最初の pushout の右因子の誘導射は零端を固定する。
方針：pushout の desc の計算。
規約：右包含は固定した左因子からの射。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の自然性。 -/
lemma fatJoinStageMapRight_inr {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) :
    pushout.inr (SSet.ι₀ (X := K) ▷ A) (fst K A) ≫ fatJoinStageMapRight K f =
      pushout.inr _ _ := pushout.inr_desc _ _ _

/-- 概要：右因子の単射は fat join の最初の pushout の単射を誘導する。
方針：零端の円柱側の正方形の pullback 性を使う。
規約：左因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の右因子のセルの包含。 -/
instance fatJoinStageMapRight_mono {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) [Mono f] :
    Mono (fatJoinStageMapRight K f) := by
  have : Mono (SSet.ι₀ (X := K) ▷ B) := (tensorRight B).map_mono _
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 K) f) := by
    change Mono ((K ⊗ (Δ[1] : SSet.{u})) ◁ f)
    exact (tensorLeft _).map_mono _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (K ◁ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 K) f) (𝟙 K) (fatJoinStageMapRight K f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_whisker_exchange SSet.ι₀ f)
  · simpa using (tensorHom_fst (𝟙 K) f).symm
  · exact fatJoinStageMapRight_inl K f
  · simpa using fatJoinStageMapRight_inr K f

/-- 概要：右因子の変化でも最初の pushout に残った一端の逆像は一致する。
方針：零端と一端が交わらないことと一端の直積の正方形を使う。
規約：右因子の射 f に単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の第二の pushout の比較。 -/
lemma fatJoinStageEnd_right_isPullback {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd K A) (K ◁ f) (fatJoinStageMapRight K f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd K B) := by
  have : Mono (SSet.ι₀ (X := K) ▷ B) := (tensorRight B).map_mono _
  have : Mono (SSet.ι₁ (X := K) ▷ B) := (tensorRight B).map_mono _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_pushout_inl_comp_of_disjoint
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap (𝟙 K) f) (𝟙 K) (fatJoinStageMapRight K f)
    (fatJoinStageMapRight_inl K f)
    (by simpa using fatJoinStageMapRight_inr K f)
    (SSet.ι₁ (X := K) ▷ A) (SSet.ι₁ (X := K) ▷ B) (K ◁ f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPullback_whisker_exchange SSet.ι₁ f)
  all_goals
    intro n a b he
    obtain ⟨⟨n⟩⟩ := n
    have hh := congrArg (fun z ↦ z.1.2 (0 : Fin (n + 1))) he
    exact (show (0 : Fin 2) ≠ 1 by decide) hh

/-- 概要：右因子の単射は fat join の単射を誘導する。
方針：最初の pushout の単射と残った端点の逆像を第二の pushout に適用する。
規約：左因子 K は任意。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の右因子のセル分解。 -/
instance fatJoinMap_right_mono {A B : SSet.{u}} (K : SSet.{u}) (f : A ⟶ B) [Mono f] :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_of_pushout_cube (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    (K ◁ f) (fatJoinStageMapRight K f) f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) f)
    (fatJoinStageEnd_right_isPullback K f)
  · simpa using (tensorHom_snd (𝟙 K) f).symm
  · apply pushout.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder, Category.assoc, reassoc_of% fatJoinStageMapRight_inl] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map (𝟙 K) f
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl, Category.assoc, reassoc_of% fatJoinStageMapRight_inr,
        Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map (𝟙 K) f
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map (𝟙 K) f

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
