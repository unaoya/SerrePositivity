module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFiber

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TautScaffold
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：simplicial replacement の底変換と taut scaffold の整合性。
方針：射列に底の関手を後合成し、係数単体を保つ四角形を各次数で pullback と確認する。
規約：底の関手にも係数図式にも充填性を要求しない。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、Remark 5.3.4.14（Tag 0376）、標準単体への scaffold 比較の還元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：底の関手は simplicial replacement の全空間の射を誘導する。
方針：底の射列に H を後合成し、始点の係数単体をそのまま用いる。
規約：始域の係数図式は H⋙F。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、底変換の比較射。 -/
@[kerodon 035X]
def simplicialReplacementBaseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement (H ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F where
  app _ := ↾fun s ↦ ⟨s.1 ⋙ H, s.2⟩
  naturality _ _ _ := rfl

/-- 概要：simplicial replacement の底変換の射は底の nerve の関手を被覆する。
方針：両辺で係数を忘れて底の射列を比較する。
規約：射影は各係数図式の標準射影。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、底変換の可換四角形。 -/
lemma simplicialReplacementBaseMap_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    simplicialReplacementBaseMap H F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (H ⋙ F) ≫ nerveMap H := rfl

/-- 概要：simplicial replacement の底変換の四角形は pullback。
方針：各次数で底の一致を代入し、同じ係数単体を新しい射列に添える。
規約：単体集合の厳密な pullback であり、同値への置換は不要。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、底の各標準単体上の比較への還元。 -/
@[kerodon 035X]
lemma simplicialReplacementBaseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (simplicialReplacementBaseMap H F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (H ⋙ F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (nerveMap H) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ h
    change (⟨σ ⋙ H, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F d.unop.len) =
        ⟨σ' ⋙ H, τ'⟩ ∧ σ = σ' at h
    rcases h with ⟨h, rfl⟩
    have hτ := eq_of_heq (Sigma.mk.inj h).2
    exact congrArg (fun q ↦ (⟨σ, q⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (H ⋙ F) d.unop.len)) hτ
  · rintro ⟨σ, τ⟩ δ h
    change σ = δ ⋙ H at h
    subst σ
    exact ⟨⟨δ, τ⟩, rfl, rfl⟩

/-- 概要：taut scaffold は通常の関手による底変換と可換。
方針：初区間の制限と係数輸送の式が H の後合成で変わらないことを使う。
規約：引き戻した図式と元の図式の両側の底変換の比較射を用いる。
使われ方：Kerodon Remark 5.3.4.14（Tag 0376）、単体上の taut scaffold の同定。 -/
lemma tautScaffold_baseMap {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (H ⋙ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap H F =
      simplicialReplacementBaseMap H F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F := rfl

/-- 概要：taut scaffold の底変換の比較四角形は pullback。
方針：各次数で底の射列を固定し、可換な単体の組から係数単体を取り出す。
規約：係数図式の充填性は不要。
使われ方：Kerodon Remark 5.3.4.14（Tag 0376）、taut scaffold の底変換を厳密に計算する。 -/
@[kerodon 0376]
lemma tautScaffold_baseMap_isPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] (H : D ⥤ C) (F : C ⥤ SSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (H ⋙ F)) (simplicialReplacementBaseMap H F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveBaseMap H F) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ h
    have hs : σ = σ' := congrArg Sigma.fst h.1
    subst σ'
    have hτ := eq_of_heq (Sigma.mk.inj h.2).2
    exact congrArg (fun q ↦ (⟨σ, q⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (H ⋙ F) d.unop.len)) hτ
  · rintro ⟨σ, ψ⟩ ⟨δ, τ⟩ h
    have hσ : σ ⋙ H = δ := congrArg Sigma.fst h
    subst δ
    refine ⟨⟨σ, τ⟩, ?_, rfl⟩
    refine Sigma.ext (by rfl) ?_
    exact (Sigma.mk.inj h).2.symm

/-- 概要：係数値の定値包含は通常の関手による底変換と可換。
方針：定値射列の後合成が像の対象の定値射列になることを関手の恒等則で示す。
規約：係数単体は同じ射を使う。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、底変換した scaffold の fiber 比較。 -/
lemma simplicialReplacementConstantLift_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) (d : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift (H ⋙ F) d ≫ simplicialReplacementBaseMap H F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementConstantLift F (H.obj d) := by
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro s
  have hσ : (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj d ⋙ H =
      (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj (H.obj d) := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp
  exact Sigma.ext hσ (HEq.rfl)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
