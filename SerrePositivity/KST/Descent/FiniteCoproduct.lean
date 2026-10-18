module

public import SerrePositivity.KST.Descent.SchemeFacts
public import Mathlib.Data.Fintype.Option

/-!
# 有限個の有限射の非交和

## 概要
有限個の有限射を同じ終域への非交和からの射にまとめても有限であることを証明する。

## 方針
有限型の添字を空と Option による帰納法で扱い、二項非交和についての Mathlib の
有限性を適用する。非交和の取り方は標準の圏論的 coproduct を保持する。

## 規約
添字の有限性は必須。無限個の有限射の非交和について有限とは主張しない。

## 使われ方
論文 定理 3.1 の W = ⊔_I Y から V への軌道射の有限性・固有性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：Option 添字の非交和を二項非交和として分解（論文 定理 3.1）。
方針：各成分への包含を用いて相互に逆な二つの射を構成する。
規約：スキームの標準の非交和の間の具体的な同型。
使われ方：有限個の軌道成分に関する帰納。 -/
noncomputable def optionCoproductIso {I : Type u} (Y : Option I → Scheme.{u}) :
    (∐ Y) ≅ Y none ⨿ (∐ fun i ↦ Y (some i)) where
  hom := Sigma.desc fun i ↦ match i with
    | none => coprod.inl
    | some j => Sigma.ι (fun i : I ↦ Y (some i)) j ≫ coprod.inr
  inv := coprod.desc (Sigma.ι _ none) (Sigma.desc fun i ↦ Sigma.ι _ (some i))
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i <;> simp
  inv_hom_id := by
    apply coprod.hom_ext
    · simp
    · apply Sigma.hom_ext
      intro i
      simp

/-- 概要：Option 非交和の分解は指定された射と両立（論文 定理 3.1）。
方針：各成分の包含との合成を検査する。
規約：単なる非交和対象の同型ではなく、終域への指定射の式。
使われ方：二項の有限射の有限性を標準の軌道射へ移す。 -/
theorem optionCoproductIso_desc {I : Type u} {X : Scheme.{u}}
    {Y : Option I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    (optionCoproductIso Y).hom ≫
        coprod.desc (f none) (Sigma.desc fun i ↦ f (some i)) = Sigma.desc f := by
  apply Sigma.hom_ext
  intro i
  cases i <;> simp [optionCoproductIso]

/-- 概要：有限個の有限射の非交和からの射は有限（論文 定理 3.1）。
方針：有限型の添字の空・Option 帰納を使い、二項非交和の有限性を適用する。
規約：源の各成分は異なってもよく、共通の終域への射を考える。
使われ方：有限個の閉切断からの軌道射の有限性。 -/
theorem finiteCoproductDesc_isFinite {I : Type u} [Finite I] {X : Scheme.{u}}
    {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsFinite (f i)] :
    IsFinite (Sigma.desc f) := by
  have h : ∀ (J : Type u) [Finite J],
      ∀ (Z : J → Scheme.{u}) (q : ∀ j, Z j ⟶ X), (∀ j, IsFinite (q j)) →
        IsFinite (Sigma.desc q) := by
    intro J _
    induction J using Finite.induction_empty_option with
    | of_equiv e ih =>
      intro Z q hq
      have finite_desc : IsFinite (Sigma.desc fun j ↦ q (e j)) := ih _ _ (fun j ↦ hq (e j))
      have eq : Sigma.desc q = (Sigma.reindex e Z).inv ≫ Sigma.desc (fun j ↦ q (e j)) := by
        apply (cancel_epi (Sigma.reindex e Z).hom).mp
        apply Sigma.hom_ext
        intro j
        simp
      have finite_comp :
          IsFinite ((Sigma.reindex e Z).inv ≫ Sigma.desc (fun j ↦ q (e j))) := by
        exact MorphismProperty.comp_mem (@IsFinite) _ _ inferInstance finite_desc
      exact eq.symm ▸ finite_comp
    | h_empty =>
      intro Z q _
      have : IsEmpty ↑(∐ Z) := ⟨fun x ↦ PEmpty.elim ((sigmaMk Z).symm x).1⟩
      infer_instance
    | h_option ih =>
      intro Z q hq
      have : IsFinite (q none) := hq none
      have : IsFinite (Sigma.desc fun j ↦ q (some j)) := ih _ _ (fun j ↦ hq (some j))
      rw [← optionCoproductIso_desc q]
      infer_instance
  exact h I Y f (fun i ↦ inferInstance)

end SerrePositivity.KST.Descent
