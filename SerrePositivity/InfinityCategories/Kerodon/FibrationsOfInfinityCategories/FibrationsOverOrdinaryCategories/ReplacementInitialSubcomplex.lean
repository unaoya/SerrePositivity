module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementAssembly
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：始対象で始まらない単体を含む部分底による replacement の pushout 分解。
方針：残りの単体を始対象の係数から組み立て、重なる部分を底の逆像で検査する。
規約：係数の Kan 性は不要。
使われ方：Kerodon Lemma 5.3.6.3（Tag 025A）、内ホーンの逆像の inner anodyne 性。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：始対象の係数による組み立てを部分底の逆像へ制限する。
方針：組み立ての底が第一射影であることを使う。
規約：部分底 A は任意。
使われ方：replacement の内ホーンへの制限と係数の直積の交わり。 -/
def replacementInitialSubcomplexMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c : C} (hc : IsInitial c) (A : (nerve C).Subcomplex) :
    (A : SSet.{u}) ⊗ F.obj c ⟶ A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) :=
  Subcomplex.lift ((A.ι ▷ F.obj c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F hc) (by
    rintro d _ ⟨⟨σ, s⟩, rfl⟩
    exact σ.property)

/-- 概要：部分底の組み立ての交わりの四角形は pullback。
方針：各次数で係数を固定し、底の単体の部分複体への所属条件を回収する。
規約：組み立て射は単射でなくてよい。
使われ方：replacement の pushout 分解の交わりの判定。 -/
lemma replacementInitialSubcomplexMap_isPullback {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c : C} (hc : IsInitial c) (A : (nerve C).Subcomplex) :
    IsPullback (replacementInitialSubcomplexMap F hc A) (A.ι ▷ F.obj c)
      (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F hc) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
    have hσ : σ.val = σ'.val := congrArg Prod.fst h.2
    have hs : s = s' := congrArg Prod.snd h.2
    exact Prod.ext (Subtype.ext hσ) hs
  · rintro ⟨v, hv⟩ ⟨σ, s⟩ h
    have hσ : σ ∈ A.obj d := by
      change v.1 ∈ A.obj d at hv
      have hvσ : v.1 = σ := congrArg Sigma.fst h
      rwa [← hvσ]
    refine ⟨(⟨σ, hσ⟩, s), ?_, rfl⟩
    exact Subtype.ext h.symm

/-- 概要：始対象以外から始まる単体を含む部分底と始対象の係数は replacement を被覆する。
方針：始対象から始まる単体は係数をそのまま移し、残りは部分底に含める。
規約：各次数の被覆条件として述べる。
使われ方：内ホーンの逆像のセル付加の共同全射性。 -/
lemma replacementInitialSubcomplex_cover {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c : C} (hc : IsInitial c) (A : (nerve C).Subcomplex)
    (hA : ∀ (d : SimplexCategoryᵒᵖ) (σ : (nerve C).obj d), σ.obj 0 ≠ c → σ ∈ A.obj d)
    (d : SimplexCategoryᵒᵖ) :
    Set.range ((A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι.app d) ⊔
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F hc).app d) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨σ, τ⟩
  by_cases hσ : σ.obj 0 = c
  · right
    let v := τ ≫ F.map (eqToHom hσ)
    refine ⟨(σ, SSet.yonedaEquiv v), ?_⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv v) ≫ F.map (hc.to (σ.obj 0)) = τ
    rw [Equiv.symm_apply_apply]
    dsimp only [v]
    have h : eqToHom hσ ≫ hc.to (σ.obj 0) = 𝟙 _ := by
      subst c
      exact hc.hom_ext _ _
    rw [Category.assoc, ← F.map_comp, h, F.map_id, Category.comp_id]
  · left
    exact ⟨⟨⟨σ, τ⟩, hA d σ hσ⟩, rfl⟩

/-- 概要：replacement は部分底の逆像と始対象の係数部分を貼り合わせた pushout。
方針：交わりの pullback と被覆、部分底の外で係数を復元できることを使う。
規約：部分底は始対象以外から始まる単体を全て含む。
使われ方：Kerodon Lemma 5.3.6.3（Tag 025A）、inner horn の逆像の幾何学的な分解。 -/
lemma replacementInitialSubcomplex_isPushout {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {c : C} (hc : IsInitial c) (A : (nerve C).Subcomplex)
    (hA : ∀ (d : SimplexCategoryᵒᵖ) (σ : (nerve C).obj d), σ.obj 0 ≠ c → σ ∈ A.obj d) :
    IsPushout (replacementInitialSubcomplexMap F hc A) (A.ι ▷ F.obj c)
      (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F hc) := by
  have hp := replacementInitialSubcomplexMap_isPullback F hc A
  apply IsPushout.of_forall_isPushout_app
  intro d
  apply Types.isPushout_of_isPullback_of_mono' (hp.app d)
    (replacementInitialSubcomplex_cover F hc A hA d)
  rintro ⟨σ, s⟩ ⟨σ', s'⟩ hs _ he
  have hσ : σ = σ' := congrArg Sigma.fst he
  subst σ'
  have hcσ : σ.obj 0 = c := by
    by_contra h
    exact hs ⟨(⟨σ, hA d σ h⟩, s), rfl⟩
  have hto : hc.to (σ.obj 0) = eqToHom hcσ.symm := hc.hom_ext _ _
  have hst := eq_of_heq (Sigma.mk.inj he).2
  change SSet.yonedaEquiv.symm s ≫ F.map (hc.to (σ.obj 0)) =
    SSet.yonedaEquiv.symm s' ≫ F.map (hc.to (σ.obj 0)) at hst
  rw [hto] at hst
  exact Prod.ext rfl (SSet.yonedaEquiv.symm.injective ((cancel_mono _).1 hst))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
