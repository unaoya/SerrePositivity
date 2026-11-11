module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinRightMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinLeftColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutFunctorColimits
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
概要：fat join の右因子の関手と連結な余極限の保存。
方針：二段の pushout の三つの関手の余極限保存を順に使う。
規約：固定した左因子に quasicategory 性は要求しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族と無限の骨格。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最初の pushout の右因子の誘導射は恒等を保つ。
方針：円柱と零端上で比較する。
規約：左因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせ関手。 -/
lemma fatJoinStageMapRight_id (A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K (𝟙 A) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage K A) := by
  apply pushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl, Category.comp_id]
    rfl
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr, Category.comp_id, Category.id_comp]

/-- 概要：最初の pushout の右因子の誘導射は合成を保つ。
方針：円柱と零端上で比較する。
規約：左因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせ関手。 -/
lemma fatJoinStageMapRight_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K g = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K (f ≫ g) := by
  apply pushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl, ← Category.assoc]
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr]

/-- 概要：固定した左因子との fat join の最初の pushout の関手。
方針：右因子の誘導射を使う。
規約：変数は右因子。
使われ方：Kerodon §4.6.2（Tag 01HM） の余極限への接続。 -/
noncomputable def fatJoinStageRightFunctor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage K A
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K f
  map_id A := fatJoinStageMapRight_id A K
  map_comp f g := (fatJoinStageMapRight_comp f g K).symm

/-- 概要：右因子の可変な円柱の零端の自然変換。
方針：円柱写像の零端の計算を使う。
規約：左因子 K を固定。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageRightZeroNat (K : SSet.{u}) :
    tensorLeft K ⟶ tensorLeft (K ⊗ (Δ[1] : SSet.{u})) where
  app A := SSet.ι₀ (X := K) ▷ A
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap_zero (𝟙 K) f).symm

/-- 概要：零端の第一射影の自然変換。
方針：第一射影の自然性を使う。
規約：右の可変因子を忘れ、左因子 K を残す。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageRightFstNat (K : SSet.{u}) :
    tensorLeft K ⟶ (Functor.const SSet.{u}).obj K where
  app A := fst K A
  naturality _ _ f := by simp

/-- 概要：可変な円柱の最初の pushout への包含の自然変換。
方針：誘導射の左包含上の計算を使う。
規約：右因子を変える。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageRightInlNat (K : SSet.{u}) :
    tensorLeft (K ⊗ (Δ[1] : SSet.{u})) ⟶ fatJoinStageRightFunctor K where
  app A := pushout.inl (SSet.ι₀ (X := K) ▷ A) (fst K A)
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl K f).symm

/-- 概要：零端の最初の pushout への包含の自然変換。
方針：誘導射の右包含上の計算を使う。
規約：標的側の零端は値 K の定数関手。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageRightInrNat (K : SSet.{u}) :
    (Functor.const SSet.{u}).obj K ⟶ fatJoinStageRightFunctor K where
  app A := pushout.inr (SSet.ι₀ (X := K) ▷ A) (fst K A)
  naturality A B f := by
    change 𝟙 K ≫ pushout.inr (SSet.ι₀ (X := K) ▷ B) (fst K B) =
      pushout.inr (SSet.ι₀ (X := K) ▷ A) (fst K A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight K f
    simpa only [Category.id_comp] using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr K f).symm

/-- 概要：右因子の第一の pushout の関手は連結な余極限を保つ。
方針：円柱と零端と直積の余極限保存を貼る。
規約：形 J は連結で、その余極限の存在を仮定する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の第一段階。 -/
instance fatJoinStageRightFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (fatJoinStageRightFunctor K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J (fatJoinStageRightZeroNat K)
    (fatJoinStageRightFstNat K) (fatJoinStageRightInlNat K) (fatJoinStageRightInrNat K)
    (fun _ ↦ IsPushout.of_hasPushout _ _)

/-- 概要：固定した左因子との fat join の関手。
方針：fat join の射への関手性を使う。
規約：右因子を変える。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと余極限。 -/
noncomputable def fatJoinRightFunctor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) f
  map_id A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_id K A
  map_comp f g := by simpa using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_comp (𝟙 K) (𝟙 K) f g).symm

/-- 概要：最初の pushout に残った一端の自然変換。
方針：一端の自然性の pullback の可換性を使う。
規約：左因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinRightEndNat (K : SSet.{u}) : tensorLeft K ⟶ fatJoinStageRightFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd K A
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd_right_isPullback K f).w.symm

/-- 概要：右の可変因子への第二射影の自然変換。
方針：第二射影の自然性を使う。
規約：標的は右因子の恒等関手。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinRightSndNat (K : SSet.{u}) : tensorLeft K ⟶ 𝟭 SSet.{u} where
  app A := snd K A
  naturality _ _ f := by simp

/-- 概要：第一の pushout から fat join への包含の自然変換。
方針：円柱と零端上で誘導射を比較する。
規約：右因子を変える。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinRightInlNat (K : SSet.{u}) : fatJoinStageRightFunctor K ⟶ fatJoinRightFunctor K where
  app A := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd K A) (snd K A)
  naturality A B f := by
    dsimp only [fatJoinRightFunctor, fatJoinStageRightFunctor]
    symm
    apply pushout.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder, Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inl] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map (𝟙 K) f
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl, Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapRight_inr, Category.id_comp] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map (𝟙 K) f

/-- 概要：右の可変因子から fat join への包含の自然変換。
方針：右包含の自然性を使う。
規約：左因子 K を固定し、右因子の包含を取る。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinRightInrNat (K : SSet.{u}) :
    𝟭 SSet.{u} ⟶ fatJoinRightFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A
  naturality A B f := by
    change f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) f
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map (𝟙 K) f).symm

/-- 概要：固定した左因子との fat join は連結な余極限を保つ。
方針：第一の pushout の余極限保存と固定因子の連結な余極限保存を貼る。
規約：形 J は連結で、その余極限が単体集合で存在する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族と無限の骨格。 -/
instance fatJoinRightFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (fatJoinRightFunctor K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J (fatJoinRightEndNat K) (fatJoinRightSndNat K)
    (fatJoinRightInlNat K) (fatJoinRightInrNat K) (fun _ ↦ IsPushout.of_hasPushout _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
