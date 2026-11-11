module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.BrownInversion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 図式モデルを仮定しない頂点ごとの Brown 分解

概要：Hovey §1.1 の Brown 分解を関手的な分解から図式全体に自然に構成する。
方針：二項余積からの射を頂点ごとに関手的に分解する。
規約：図式圏のモデル構造も射影 cofibrancy も仮定しない。
使われ方：重み付き frame Hom の係数に関する弱同値不変性。
-/

@[expose] public section

noncomputable section

universe u v w t u' v'

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory Limits HomotopicalAlgebra

variable (K : Type w) [Category.{t} K]
  {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D]

/-- 概要：頂点ごとの自明 cofibration の反転は cofibrant 値図式の弱同値へ延びる。
方針：関手的な分解による自然な Brown 分解の二つの包含を使う（Hovey §1.1）。
規約：cofibrant 条件は頂点ごとでよく、図式モデル構造は不要。
使われ方：射影 cofibrant 重みの frame Hom の始域不変性。 -/
lemma map_isIso_of_pointwise_cofibrant
    (fact : MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C))
    (T : (K ⥤ C)ᵒᵖ ⥤ D)
    (hT : ∀ {X Y : K ⥤ C} (i : X ⟶ Y),
      (∀ k, trivialCofibrations C (i.app k)) → IsIso (T.map i.op))
    {X Y : K ⥤ C} (f : X ⟶ Y)
    (hX : ∀ k, IsCofibrant (X.obj k)) (hY : ∀ k, IsCofibrant (Y.obj k))
    (hf : ∀ k, weakEquivalences C (f.app k)) : IsIso (T.map f.op) := by
  let d := (fact.functorCategory K).factorizationData (coprod.desc f (𝟙 Y))
  let i : X ⟶ d.Z := coprod.inl ≫ d.i
  let s : Y ⟶ d.Z := coprod.inr ≫ d.i
  have ip : i ≫ d.p = f := by
    dsimp only [i]
    rw [Category.assoc, d.fac, coprod.inl_desc]
  have sp : s ≫ d.p = 𝟙 Y := by
    dsimp only [s]
    rw [Category.assoc, d.fac, coprod.inr_desc]
  have hi : ∀ k, trivialCofibrations C (i.app k) := by
    intro k
    have : IsCofibrant (Y.obj k) := hY k
    let ev := (evaluation K C).obj k
    have hc : Cofibration ((coprod.inl : X ⟶ X ⨿ Y).app k) := by
      change Cofibration (ev.map coprod.inl)
      rw [← coprodComparison_inl]
      have : IsCofibrant (ev.obj Y) := hY k
      have : Cofibration (coprod.inl : ev.obj X ⟶ ev.obj X ⨿ ev.obj Y) := inferInstance
      have : IsIso (coprodComparison ev X Y) := inferInstance
      infer_instance
    have : Cofibration (d.i.app k) := ⟨d.hi k⟩
    have : WeakEquivalence (d.p.app k) := ⟨(d.hp k).2⟩
    have : WeakEquivalence (f.app k) := ⟨hf k⟩
    have : WeakEquivalence (i.app k) := weakEquivalence_of_postcomp_of_fac (congr_app ip k)
    exact ⟨(cofibration_iff _).mp (show Cofibration (i.app k) from by
      dsimp only [i, NatTrans.comp_app]
      infer_instance), mem_weakEquivalences _⟩
  have hs : ∀ k, trivialCofibrations C (s.app k) := by
    intro k
    have : IsCofibrant (X.obj k) := hX k
    let ev := (evaluation K C).obj k
    have hc : Cofibration ((coprod.inr : Y ⟶ X ⨿ Y).app k) := by
      change Cofibration (ev.map coprod.inr)
      rw [← coprodComparison_inr]
      have : IsCofibrant (ev.obj X) := hX k
      have : Cofibration (coprod.inr : ev.obj Y ⟶ ev.obj X ⨿ ev.obj Y) := inferInstance
      have : IsIso (coprodComparison ev X Y) := inferInstance
      infer_instance
    have : Cofibration (d.i.app k) := ⟨d.hi k⟩
    have : WeakEquivalence (d.p.app k) := ⟨(d.hp k).2⟩
    have : WeakEquivalence (s.app k) := weakEquivalence_of_postcomp_of_fac (congr_app sp k)
    exact ⟨(cofibration_iff _).mp (show Cofibration (s.app k) from by
      dsimp only [s, NatTrans.comp_app]
      infer_instance), mem_weakEquivalences _⟩
  have : IsIso (T.map i.op) := hT i hi
  have : IsIso (T.map s.op) := hT s hs
  have hp : T.map d.p.op ≫ T.map s.op = 𝟙 _ := by
    rw [← T.map_comp]
    change T.map (s ≫ d.p).op = _
    rw [sp]
    exact T.map_id _
  have he : T.map d.p.op = inv (T.map s.op) := by
    apply (cancel_mono (T.map s.op)).mp
    simpa only [IsIso.inv_hom_id] using hp
  have : IsIso (T.map d.p.op) := by rw [he]; infer_instance
  have hpif : T.map d.p.op ≫ T.map i.op = T.map f.op := by
    rw [← T.map_comp]
    exact congrArg T.map (congrArg Quiver.Hom.op ip)
  rw [← hpif]
  infer_instance

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
