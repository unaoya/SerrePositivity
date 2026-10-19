module

public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.KanEquivalencePrismExtension
public import SerrePositivity.InfinityCategories.F1B.KanEquivalencePrismInverting

/-!
概要：可逆 path による置換の圏論的同値に対する右持ち上げ。
方針：元の図式を延長し、両端固定の prism の可逆性を制限から反映する。
規約：元の関手には fibration 性を要求しない。
使われ方：相対 Kan 拡張を一般の関手から持ち上げ可能な関手へ還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定部分の可逆 path を両端固定で全体へ延長する。
方針：prism を延長した後、その全垂直辺の可逆性を前合成同値で反映する。
規約：端点と指定部分への制限は厳密な等式。
使われ方：可逆 path 置換の引き戻しへの持ち上げ。 -/
lemma exists_kanEquivalencePath_extension
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) [Mono i]
    (hi : IsPrecompositionEquivalence i) (a : A ⟶ equivalencePath X) (f g : B ⟶ X)
    (h₀ : a ≫ equivalencePathEndpoint X 0 = i ≫ f)
    (h₁ : a ≫ equivalencePathEndpoint X 1 = i ≫ g) :
    ∃ b : B ⟶ equivalencePath X, i ≫ b = a ∧
      b ≫ equivalencePathEndpoint X 0 = f ∧ b ≫ equivalencePathEndpoint X 1 = g := by
  let H := uncurry (a ≫ equivalencePathι X)
  have he (k : Fin 2) : prismEndpoint k A ≫ H = a ≫ equivalencePathEndpoint X k := by
    rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  obtain ⟨G, hG, hG₀, hG₁⟩ :=
    exists_kanPrism_extension_of_precompositionEquivalence i hi f g H
      ((he 0).trans h₀) ((he 1).trans h₁)
  have hv : ∀ b, IsEquivalencePathVertex ((curry G).app (Opposite.op ⦋0⦌) b) := by
    apply kanPrism_pointwiseInvertible_of_restriction i hi G
    rw [hG]
    intro x
    change IsEquivalencePathVertex ((curry (uncurry (a ≫ equivalencePathι X))).app _ x)
    rw [curry_uncurry]
    exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
  let b := fullSubcomplexLift IsEquivalencePathVertex (curry G) hv
  have hb : b ≫ equivalencePathι X = curry G := fullSubcomplexLift_ι _ _ _
  refine ⟨b, ?_, ?_, ?_⟩
  · have : Mono (equivalencePathι X) := by unfold equivalencePathι; infer_instance
    apply (cancel_mono (equivalencePathι X)).mp
    rw [Category.assoc, hb]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, hG]
  · change b ≫ equivalencePathι X ≫ evaluateFunctorAt _ = f
    rw [← Category.assoc, hb, curry_evaluateFunctorAt_interval, hG₀]
  · change b ≫ equivalencePathι X ≫ evaluateFunctorAt _ = g
    rw [← Category.assoc, hb, curry_evaluateFunctorAt_interval, hG₁]

/-- 概要：任意の関手の可逆 path 置換は単射な前合成同値を右に持ち上げる。
方針：元の図式を延長し、指定した終点の図式への可逆 path を延長して引き戻す。
規約：元の両圏の quasicategory 性のみを要求する。
使われ方：一般の関手上の相対 Kan 拡張の存在定理への因子分解。 -/
lemma kanEquivalenceLifting_equivalencePathReplacementMap
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E) :
    KanEquivalenceLifting (equivalencePathReplacementMap U) := by
  intro A B i hm hi
  have : Mono i := hm
  constructor
  intro a b sq
  obtain ⟨v, hv⟩ := pre_surjective_of_essentiallySurjective i
    (hi D).choose.isEssentiallySurjective
    (functorVertex (a ≫ equivalencePathReplacementProjection U))
  obtain ⟨c, rfl⟩ := (functorVertexEquiv B D).surjective v
  have hc : i ≫ c = a ≫ equivalencePathReplacementProjection U := by
    apply (functorVertexEquiv A D).injective
    exact hv
  let a' := a ≫ pullback.fst (equivalencePathEndpoint E 0) U
  have h₀ : a' ≫ equivalencePathEndpoint E 0 = i ≫ c ≫ U := by
    dsimp [a']
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (a ≫ equivalencePathReplacementProjection U) ≫ U = i ≫ c ≫ U
    rw [← hc, Category.assoc]
  have h₁ : a' ≫ equivalencePathEndpoint E 1 = i ≫ b := sq.w
  obtain ⟨p, hp, hp₀, hp₁⟩ :=
    exists_kanEquivalencePath_extension i hi a' (c ≫ U) b h₀ h₁
  let l : B ⟶ equivalencePathReplacement U := pullback.lift p c hp₀
  exact ⟨⟨l, by
    apply pullback.hom_ext
    · simpa only [Category.assoc, l, pullback.lift_fst] using hp
    · simpa only [Category.assoc, l, pullback.lift_snd,
        equivalencePathReplacementProjection] using hc,
    by
      change l ≫ pullback.fst (equivalencePathEndpoint E 0) U ≫
        equivalencePathEndpoint E 1 = b
      rw [← Category.assoc, pullback.lift_fst]
      exact hp₁⟩⟩

/-- 概要：可逆 path 置換の定値 path による切断は圏論的同値。
方針：自明 Kan fibration である射影との合成が恒等射であることに二対三則を使う。
規約：切断と置換された関手の合成は元の関手に厳密に等しい。
使われ方：右持ち上げ可能な関手による因子分解を同値経由で与える。 -/
lemma kanEquivalencePathReplacementSection_isQCatEquivalence
    {D E : SSet.{u}} [Quasicategory D] [Quasicategory E] (U : D ⟶ E) :
    IsQCatEquivalence (equivalencePathReplacementSection U) := by
  apply (isQCatEquivalence_of_trivialKanFibration
    (equivalencePathReplacementProjection U)).cancel_right
  rw [equivalencePathReplacementSection_projection]
  exact (QCatEquivalence.refl D).isQCatEquivalence

end SerrePositivity.InfinityCategories.F1B
