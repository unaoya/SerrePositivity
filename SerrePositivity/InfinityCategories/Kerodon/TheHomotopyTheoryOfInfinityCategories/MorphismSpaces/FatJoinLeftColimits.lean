module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinLeftMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutFunctorColimits
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
概要：fat join の左因子の関手と連結な余極限の保存。
方針：二段の pushout の三つの関手の余極限保存を順に使う。
規約：固定した右因子に quasicategory 性は要求しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族と無限の骨格。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最初の pushout の左因子の誘導射は恒等を保つ。
方針：円柱と零端上で比較する。
規約：右因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせ関手。 -/
lemma fatJoinStageMapLeft_id (A K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft (𝟙 A) K = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage A K) := by
  apply pushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl, Category.comp_id]
    rfl
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr, Category.comp_id, Category.id_comp]

/-- 概要：最初の pushout の左因子の誘導射は合成を保つ。
方針：円柱と零端上で比較する。
規約：右因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせ関手。 -/
lemma fatJoinStageMapLeft_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft f K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft g K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft (f ≫ g) K := by
  apply pushout.hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl, ← Category.assoc]
    rfl
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr, ← Category.assoc]

/-- 概要：固定した右因子との fat join の最初の pushout の関手。
方針：左因子の誘導射を使う。
規約：変数は左因子。
使われ方：Kerodon §4.6.2（Tag 01HM） の余極限への接続。 -/
noncomputable def fatJoinStageLeftFunctor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage A K
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft f K
  map_id A := fatJoinStageMapLeft_id A K
  map_comp f g := (fatJoinStageMapLeft_comp f g K).symm

/-- 概要：左因子の可変な円柱の零端の自然変換。
方針：円柱写像の零端の計算を使う。
規約：右因子 K を固定。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageLeftZeroNat (K : SSet.{u}) :
    tensorRight K ⟶ tensorRight (Δ[1] : SSet.{u}) ⋙ tensorRight K where
  app A := SSet.ι₀ (X := A) ▷ K
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinderMap_zero f (𝟙 K)).symm

/-- 概要：零端の第一射影の自然変換。
方針：第一射影の自然性を使う。
規約：右因子 K を忘れる。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageLeftFstNat (K : SSet.{u}) : tensorRight K ⟶ 𝟭 SSet.{u} where
  app A := fst A K
  naturality _ _ f := whiskerRight_fst f K

/-- 概要：可変な円柱の最初の pushout への包含の自然変換。
方針：誘導射の左包含上の計算を使う。
規約：左因子を変える。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageLeftInlNat (K : SSet.{u}) :
    tensorRight (Δ[1] : SSet.{u}) ⋙ tensorRight K ⟶ fatJoinStageLeftFunctor K where
  app A := pushout.inl (SSet.ι₀ (X := A) ▷ K) (fst A K)
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl f K).symm

/-- 概要：零端の最初の pushout への包含の自然変換。
方針：誘導射の右包含上の計算を使う。
規約：左因子は恒等関手。
使われ方：Kerodon §4.6.2（Tag 01HM） の第一の関手の pushout。 -/
noncomputable def fatJoinStageLeftInrNat (K : SSet.{u}) : 𝟭 SSet.{u} ⟶ fatJoinStageLeftFunctor K where
  app A := pushout.inr (SSet.ι₀ (X := A) ▷ K) (fst A K)
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr f K).symm

/-- 概要：左因子の第一の pushout の関手は余極限を保つ。
方針：円柱と零端と直積の余極限保存を貼る。
規約：形 J の余極限の存在を仮定する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の第一段階。 -/
instance fatJoinStageLeftFunctor_preservesColimitsOfShape (K : SSet.{u})
    (J : Type*) [Category* J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (fatJoinStageLeftFunctor K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J (fatJoinStageLeftZeroNat K)
    (fatJoinStageLeftFstNat K) (fatJoinStageLeftInlNat K) (fatJoinStageLeftInrNat K)
    (fun _ ↦ IsPushout.of_hasPushout _ _)

/-- 概要：固定した右因子との fat join の関手。
方針：fat join の射への関手性を使う。
規約：左因子を変える。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルと余極限。 -/
noncomputable def fatJoinLeftFunctor (K : SSet.{u}) : SSet.{u} ⥤ SSet.{u} where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap f (𝟙 K)
  map_id A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_id A K
  map_comp f g := by simpa using (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap_comp f g (𝟙 K) (𝟙 K)).symm

/-- 概要：最初の pushout に残った一端の自然変換。
方針：一端の自然性の pullback の可換性を使う。
規約：右因子 K を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinLeftEndNat (K : SSet.{u}) : tensorRight K ⟶ fatJoinStageLeftFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd A K
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd_left_isPullback f K).w.symm

/-- 概要：右因子への第二射影の自然変換。
方針：第二射影の自然性を使う。
規約：標的は値 K の定数関手。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinLeftSndNat (K : SSet.{u}) : tensorRight K ⟶ (Functor.const SSet.{u}).obj K where
  app A := snd A K
  naturality _ _ f := by simp

/-- 概要：第一の pushout から fat join への包含の自然変換。
方針：円柱と零端上で誘導射を比較する。
規約：左因子を変える。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinLeftInlNat (K : SSet.{u}) : fatJoinStageLeftFunctor K ⟶ fatJoinLeftFunctor K where
  app A := pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageEnd A K) (snd A K)
  naturality A B f := by
    dsimp only [fatJoinLeftFunctor, fatJoinStageLeftFunctor]
    symm
    apply pushout.hom_ext
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder, Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inl] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_map f (𝟙 K)
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl, Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStageMapLeft_inr] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map f (𝟙 K)

/-- 概要：固定した右因子から fat join への包含の自然変換。
方針：右包含の自然性を使う。
規約：左因子を変えても右因子は固定。
使われ方：Kerodon §4.6.2（Tag 01HM） の第二の関手の pushout。 -/
noncomputable def fatJoinLeftInrNat (K : SSet.{u}) :
    (Functor.const SSet.{u}).obj K ⟶ fatJoinLeftFunctor K where
  app A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K
  naturality A B f := by
    change 𝟙 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr B K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap f (𝟙 K)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map f (𝟙 K)).symm

/-- 概要：単体集合の定数関手は連結な形の余極限を保つ。
方針：定数図式の恒等の cocone は連結な形で余極限になる。
規約：形 J は連結。
使われ方：Kerodon §4.6.2（Tag 01HM） の固定因子を持つ関手の余極限。 -/
instance constantSSetFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] :
    PreservesColimitsOfShape J ((Functor.const SSet.{u}).obj K) :=
  ⟨fun {F} ↦ ⟨fun {c} _ ↦ ⟨isColimitConstCocone J K⟩⟩⟩

/-- 概要：固定した右因子との fat join は連結な余極限を保つ。
方針：第一の pushout の余極限保存と固定因子の連結な余極限保存を貼る。
規約：形 J は連結で、その余極限が単体集合で存在する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセルの族と無限の骨格。 -/
instance fatJoinLeftFunctor_preservesConnectedColimits (K : SSet.{u})
    (J : Type*) [Category* J] [IsConnected J] [HasColimitsOfShape J SSet.{u}] :
    PreservesColimitsOfShape J (fatJoinLeftFunctor K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.preservesColimitsOfShape_of_pointwise_pushout J (fatJoinLeftEndNat K) (fatJoinLeftSndNat K)
    (fatJoinLeftInlNat K) (fatJoinLeftInrNat K) (fun _ ↦ IsPushout.of_hasPushout _ _)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
