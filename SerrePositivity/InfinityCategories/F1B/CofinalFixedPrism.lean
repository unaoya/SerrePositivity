module

public import SerrePositivity.InfinityCategories.F1B.CofinalFunctorSpace
public import SerrePositivity.InfinityCategories.Core.PrismBoundaryExtension
public import SerrePositivity.InfinityCategories.Core.LeftPrism

/-!
概要：left fibration に沿う、単射で指定した部分を全時間で固定した prism の持ち上げ。
方針：先頭の一次ホーンと単射の pushout-product に対して持ち上げる。
規約：指定部分は境界に限らず任意の単射。底・全空間の quasicategory 性は不要。
使われ方：標準単体の終点 fiber を固定する収縮の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibration は任意の単射上で指定した prism と先頭の射を同時に持ち上げる。
方針：二つの射を pushout に貼り、left anodyne な比較射の持ち上げを使う。
規約：全時間で底を指定し、元の指定部分を厳密に保つ。
使われ方：終点 fiber の包含を固定する収縮。 -/
lemma leftFibration_lift_fixed_prism {A D X B : SSet.{u}}
    (i : A ⟶ D) [Mono i] (p : X ⟶ B) [LeftFibration p]
    (G : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (F₀ : D ⟶ X)
    (β : (Δ[1] : SSet.{u}) ⊗ D ⟶ B)
    (h₀ : prismEndpoint 0 A ≫ G = i ≫ F₀)
    (hG : G ≫ p = (Δ[1] ◁ i) ≫ β)
    (hβ : F₀ ≫ p = prismEndpoint 0 D ≫ β) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ D ⟶ X,
      (Δ[1] ◁ i) ≫ H = G ∧ prismEndpoint 0 D ≫ H = F₀ ∧ H ≫ p = β := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i
  have hw : ((horn 1 0).ι ▷ A) ≫ G =
      ((horn 1 0 : SSet.{u}) ◁ i) ≫ (snd (horn 1 0 : SSet.{u}) D ≫ F₀) := by
    rw [hornOneFirst_prism_factorization]
    simp only [Category.assoc, h₀]
    simpa only [Category.assoc] using
      (congrArg (fun k ↦ k ≫ F₀) (whiskerLeft_snd (horn 1 0 : SSet.{u}) i)).symm
  let a := sq.isPushout.desc G (snd (horn 1 0 : SSet.{u}) D ≫ F₀) hw
  have ha : a ≫ p = sq.ι ≫ β := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hG
    · rw [← Category.assoc, sq.isPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      change (snd (horn 1 0 : SSet.{u}) D ≫ F₀) ≫ p = ((horn 1 0).ι ▷ D) ≫ β
      rw [Category.assoc, hβ, hornOneFirst_prism_factorization, Category.assoc]
  have := leftAnodyneExtensions_pushoutObjObj_point i sq p (LeftFibration.mem (p := p))
  let hs : CommSq a sq.ι p β := ⟨ha⟩
  refine ⟨hs.lift, ?_, ?_, hs.fac_right⟩
  · change ((curriedTensor SSet.{u}).obj (Δ[1] : SSet.{u})).map i ≫ hs.lift = G
    rw [← sq.inl_ι, Category.assoc, hs.fac_left, sq.isPushout.inl_desc]
  · have he : ((horn 1 0).ι ▷ D) ≫ hs.lift =
        snd (horn 1 0 : SSet.{u}) D ≫ F₀ := by
      change ((curriedTensor SSet.{u}).map (horn 1 0).ι).app D ≫ hs.lift = _
      rw [← sq.inr_ι, Category.assoc, hs.fac_left, sq.isPushout.inr_desc]
    have he' := congrArg (fun k ↦ hornOneFirstSection D ≫ k) he
    simpa only [← Category.assoc, hornOneFirstSection_ι, hornOneFirstSection_snd,
      Category.id_comp] using he'

end SerrePositivity.InfinityCategories
