module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：weighted nerve は通常の圏の関手に沿う底変換と厳密に整合する。
方針：射列に底の関手を後合成し、各次数で重み付き図式を保つ pullback を確認する。
規約：底変換の関手や係数の充填性には制約を課さない。
使われ方：Kerodon §5.3.3（Tag 025W）、相対ホーンを底の標準単体上の係数図式へ移す操作。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数図式の底の関手は weighted nerve の全空間の射を誘導する。
方針：底の射列に H を後合成し、重み付き自然変換はそのまま保つ。
規約：係数図式は F、引き戻した図式は H⋙F。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の底変換の比較射。 -/
def weightedNerveBaseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (H ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F where
  app _ := ↾fun s ↦ ⟨s.1 ⋙ H, s.2⟩
  naturality _ _ _ := rfl

/-- 概要：weighted nerve の底変換の比較射は元の底の関手を被覆する。
方針：底の合成可能射列だけを取り出して計算する。
規約：二つの射影はそれぞれ H⋙F と F の weighted nerve の射影。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の底変換の可換四角形。 -/
lemma weightedNerveBaseMap_projection {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    weightedNerveBaseMap H F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (H ⋙ F) ≫ nerveMap H := rfl

/-- 概要：weighted nerve の底変換の四角形は pullback。
方針：各次数で、引き戻した射列上の図式と二つの可換な単体の組を往復させる。
規約：充填性や単射性を前提にしない厳密な pullback。
使われ方：Kerodon §5.3.3（Tag 025W）、底の標準単体上へ相対的な問題を還元する。 -/
lemma weightedNerveBaseMap_isPullback {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (weightedNerveBaseMap H F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (H ⋙ F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (nerveMap H) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ h
    change (⟨σ ⋙ H, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F d.unop.len) = ⟨σ' ⋙ H, τ'⟩ ∧ σ = σ' at h
    rcases h with ⟨h, rfl⟩
    have hτ := eq_of_heq (Sigma.mk.inj h).2
    exact congrArg (fun q ↦ (⟨σ, q⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex (H ⋙ F) d.unop.len)) hτ
  · rintro ⟨σ, τ⟩ δ h
    change σ = δ ⋙ H at h
    subst σ
    exact ⟨⟨δ, τ⟩, rfl, rfl⟩

/-- 概要：底変換の可換な二つの図式は引き戻した係数の weighted nerve へ持ち上がる。
方針：weighted nerve の底変換の pullback の普遍性を使う。
規約：パラメータ T は任意の単体集合。
使われ方：Kerodon §5.3.3（Tag 025W）、ホーンの図式を底の単体上の weighted nerve へ移す。 -/
noncomputable def weightedNerveBaseChangeLift {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap H) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (H ⋙ F) :=
  (weightedNerveBaseMap_isPullback H F).lift a b h

/-- 概要：底変換の持ち上げは元の weighted nerve の図式を保つ。
方針：pullback の第一射影の計算則を使う。
規約：元の図式 a に厳密に一致する。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の Kan 充填を元の全空間のホーンと比較する式。 -/
lemma weightedNerveBaseChangeLift_base {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap H) :
    weightedNerveBaseChangeLift H F a b h ≫ weightedNerveBaseMap H F = a :=
  (weightedNerveBaseMap_isPullback H F).lift_fst _ _ _

/-- 概要：底変換の持ち上げは指定した新しい底の図式を被覆する。
方針：pullback の第二射影の計算則を使う。
規約：新しい底の図式 b に厳密に一致する。
使われ方：Kerodon §5.3.3（Tag 025W）、標準単体の最後の頂点への係数評価の底の固定。 -/
lemma weightedNerveBaseChangeLift_projection {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) {T : SSet.{u}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (b : T ⟶ nerve D)
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = b ≫ nerveMap H) :
    weightedNerveBaseChangeLift H F a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (H ⋙ F) = b :=
  (weightedNerveBaseMap_isPullback H F).lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
