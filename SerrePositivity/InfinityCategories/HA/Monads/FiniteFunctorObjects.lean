module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma

/-!
概要：有限な対象の範囲に値を持つ有限圏からの実関手は有限個である。
方針：対象の関数と全射の関数を依存和へ符号化し、関手の法則の証明非依存性を使う。
規約：対象・射の有限性は仮定の型で明示する一般の補題。
使われ方：Riehl–Verity Proposition 4.2.15の各幅での実関手の有限性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限な対象の範囲にある実関手の全体は有限。
方針：対象を範囲の部分型へ取り、全射の作用との依存和に単射で入れる。
規約：関手の実作用を保持し、同型類に落とさない。使われ方：Riehl–Verity §4.2の有限性。 -/
lemma finite_functors_of_objectwise_finite {I : Type u₁} {D : Type u₂}
    [Category.{v₁} I] [Category.{v₂} D] [Finite I]
    [∀ i j : I, Finite (i ⟶ j)] [∀ A B : D, Finite (A ⟶ B)]
    (P : D → Prop) [Finite {A : D // P A}] :
    Finite {F : I ⥤ D // ∀ i, P (F.obj i)} := by
  let encode : {F : I ⥤ D // ∀ i, P (F.obj i)} →
      Σ f : I → {A : D // P A}, ∀ i j : I, (i ⟶ j) → ((f i).val ⟶ (f j).val) :=
    fun F => ⟨fun i => ⟨F.val.obj i, F.property i⟩, fun _ _ f => F.val.map f⟩
  apply Finite.of_injective encode
  rintro ⟨⟨fo, fm, fi, fc⟩, hf⟩ ⟨⟨go, gm, gi, gc⟩, hg⟩ he
  have ho : fo = go := by
    funext i
    exact congrArg Subtype.val (congrFun (congrArg Sigma.fst he) i)
  cases ho
  have hm : (fun (i j : I) (f : i ⟶ j) => fm f) =
      (fun (i j : I) (f : i ⟶ j) => gm f) := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hemap : @fm = @gm := by
    funext i j f
    exact congrFun (congrFun (congrFun hm i) j) f
  cases hemap
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
