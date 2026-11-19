module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformModule
public import Mathlib.Algebra.Exact.Basic

/-!
概要：Stacks 0815 の純変換に対する線形写像と完全性の基本性質。
方針：代表元と境界ねじれの冪消滅判定へ還元する。
規約：完全性の保存には右側の境界元の正則作用を明示して仮定する。
使われ方：KST §5、平坦化の加群の完全列への適用の準備。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] (f : R)
variable {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/--
概要：純変換に誘導される写像は代表元上で元の写像と一致する。
方針：商写像の定義を展開する。
規約：Stacks 0815、同じ境界元を両側で使用する。
使われ方：純変換の完全性の代表元による検証。
-/
theorem modulePureTransformMap_mk (g : M →ₗ[R] N) (m : M) :
    modulePureTransformMap f g (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (g m) := rfl

/--
概要：単射な線形写像の純変換は単射。
方針：像の境界ねじれの消滅を単射性で元へ戻す。
規約：Stacks 0815、環・加群の有限性は不要。
使われ方：純変換の左側の単射性。
-/
theorem modulePureTransformMap_injective (g : M →ₗ[R] N) (hg : Function.Injective g) :
    Function.Injective (modulePureTransformMap f g) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hm : g m ∈ boundaryTorsion f N := (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f N _).mp hm
  apply (mem_boundaryTorsion_iff f M _).mpr
  exact ⟨n, hg (by rw [g.map_smul, hn, g.map_zero])⟩

/--
概要：全射な線形写像の純変換は全射。
方針：商の代表元を元の全射で持ち上げる。
規約：Stacks 0815、ねじれ部分の全射性は仮定しない。
使われ方：純変換の右側の全射性。
-/
theorem modulePureTransformMap_surjective (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    Function.Surjective (modulePureTransformMap f g) := by
  intro x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f N) x
  obtain ⟨m, rfl⟩ := hg n
  exact ⟨Submodule.Quotient.mk m, rfl⟩

/--
概要：右端で境界元が正則に作用する完全列は純変換後も中央で完全。
方針：右端のねじれが零であることを使い、代表元を元の完全列で持ち上げる。
規約：Stacks 0815、右端の正則作用を省略して完全性を主張しない。
使われ方：平坦な余核を持つ加群列の純変換。
-/
theorem modulePureTransformMap_exact_of_isSMulRegular
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) (hex : Function.Exact g h)
    (hf : IsSMulRegular P f) :
    Function.Exact (modulePureTransformMap f g) (modulePureTransformMap f h) := by
  intro x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f N) x
  constructor
  · intro hn
    have ht : h n ∈ boundaryTorsion f P := (Submodule.Quotient.mk_eq_zero _).mp hn
    rw [boundaryTorsion_eq_bot_of_isSMulRegular f P hf] at ht
    obtain ⟨m, hm⟩ := (hex n).mp ht
    exact ⟨Submodule.Quotient.mk m, congrArg Submodule.Quotient.mk hm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
    rw [← hx, modulePureTransformMap_mk, modulePureTransformMap_mk]
    have hz := (hex (g m)).mpr ⟨m, rfl⟩
    simp only [hz, Submodule.Quotient.mk_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
