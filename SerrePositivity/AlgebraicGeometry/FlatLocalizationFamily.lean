module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Flat.Localization

/-!
概要：KST §5、Stacks 0815 の添字付き局所化族による加群の平坦性の判定。
方針：単位イデアルを生成する元の族を集合の形の既存の局所判定へ移す。
規約：族の添字は重複してよく有限性も要求しない。
使われ方：blowup の生成元チャートとの重なりによる平坦性判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/--
概要：単位イデアルを生成する族の各局所化で平坦なら元の加群も平坦。
方針：元の値の集合の各点に添字を選び、集合による局所判定を使う。
規約：KST §5、Stacks 0815、局所化の加群と実際の写像を入力する。
使われ方：生成元チャートの重なり上で平坦性を検証する。
-/
theorem flat_of_isLocalized_family_span (c : ι → R)
    (hc : Ideal.span (Set.range c) = ⊤) (N : ι → Type*)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (η : ∀ i, M →ₗ[R] N i)
    [∀ i, IsLocalizedModule.Away (c i) (η i)] [∀ i, Module.Flat R (N i)] :
    Module.Flat R M := by
  classical
  let idx (r : Set.range c) : ι := Classical.choose r.property
  have hi (r : Set.range c) : c (idx r) = r.val := Classical.choose_spec r.property
  have (r : Set.range c) : IsLocalizedModule.Away r.val (η (idx r)) := by
    rw [← hi r]
    infer_instance
  exact Module.flat_of_isLocalized_span (R := R) (S := R) (M := M) (Set.range c) hc
    (fun r => N (idx r)) (fun r => η (idx r)) (fun _ => inferInstance)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
