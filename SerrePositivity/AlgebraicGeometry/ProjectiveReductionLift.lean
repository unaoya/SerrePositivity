module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.FlatQuotientKernel
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
概要：KST §5、Stacks 05CG の剰余の右逆からの射影加群上の自己準同型。
方針：剰余の右逆を持ち上げ、イデアル倍に値を持つ誤差を再び持ち上げて補正する。
規約：自由加群より一般の射影的な始域を許す。
使われ方：冪零剰余の射影性から全射の実際の右逆を作る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：全射のイデアル倍への制限も全射。
方針：イデアル倍の生成元の係数を固定し、残る元を元の全射で持ち上げる。
規約：KST §5、Stacks 05CG・05D3、平坦性は不要。
使われ方：剰余で消える誤差をイデアル倍の中で補正する。
-/
theorem exists_smul_top_preimage_of_surjective
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (I : Ideal R) (m : M) (hm : m ∈ I • (⊤ : Submodule R M)) :
    ∃ x ∈ I • (⊤ : Submodule R F), π x = m := by
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro r hr m hm
    obtain ⟨x, rfl⟩ := hπ m
    exact ⟨r • x, Submodule.smul_mem_smul hr (Submodule.mem_top), π.map_smul r x⟩
  · intro m n hm hn
    obtain ⟨x, hx, rfl⟩ := hm
    obtain ⟨y, hy, rfl⟩ := hn
    exact ⟨x + y, (I • (⊤ : Submodule R F)).add_mem hx hy, π.map_add x y⟩

/--
概要：射影的な始域の全射の剰余に指定した右逆を、元の全射を保つ自己準同型へ持ち上げる。
方針：剰余右逆の持ち上げとイデアル倍の誤差の持ち上げを加える。
規約：KST §5、Stacks 05CG、完備性・冪零性・平坦性はこの構成には不要。
使われ方：平坦な終域の場合、この自己準同型は核をそのイデアル倍へ送る。
-/
theorem exists_endomorphism_lifting_reduction_section
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F] [Module.Projective R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (I : Ideal R)
    (s : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I]
      (F ⧸ (I • (⊤ : Submodule R F))))
    (hs : (π.reduceModIdeal I).comp s = LinearMap.id) :
    ∃ e : F →ₗ[R] F, π.comp e = π ∧
      (I • (⊤ : Submodule R F)).mkQ.comp e =
        (s.restrictScalars R).comp ((I • (⊤ : Submodule R M)).mkQ.comp π) := by
  let QF := I • (⊤ : Submodule R F)
  let QM := I • (⊤ : Submodule R M)
  let g := (s.restrictScalars R).comp (QM.mkQ.comp π)
  obtain ⟨e₀, he₀⟩ := Module.projective_lifting_property QF.mkQ g
    (Submodule.mkQ_surjective QF)
  let d := π - π.comp e₀
  have hd (x : F) : d x ∈ QM := by
    change π x - π (e₀ x) ∈ QM
    have hx : QM.mkQ (π (e₀ x)) = QM.mkQ (π x) := by
      have hh := congrArg (fun f => f (QM.mkQ (π x))) hs
      have he := congrArg (fun f => f x) he₀
      change QF.mkQ (e₀ x) = s (QM.mkQ (π x)) at he
      change (π.reduceModIdeal I) (s (QM.mkQ (π x))) = QM.mkQ (π x) at hh
      rw [← he] at hh
      exact hh
    have hz : QM.mkQ (π x - π (e₀ x)) = 0 := by rw [map_sub, hx, sub_self]
    change π x - π (e₀ x) ∈ LinearMap.ker QM.mkQ at hz
    rwa [Submodule.ker_mkQ] at hz
  let πI : QF →ₗ[R] QM := (π.comp QF.subtype).codRestrict QM (by
    intro x
    change π x.val ∈ QM
    refine Submodule.smul_induction_on x.property ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    · intro z w hz hw
      simpa using QM.add_mem hz hw)
  have hπI : Function.Surjective πI := by
    intro m
    obtain ⟨x, hx, hxm⟩ := exists_smul_top_preimage_of_surjective π hπ I m.val m.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxm⟩
  obtain ⟨c, hc⟩ := Module.projective_lifting_property πI (d.codRestrict QM hd) hπI
  refine ⟨e₀ + QF.subtype.comp c, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    have hx := congrArg (fun f => (f x : M)) hc
    change π (c x).val = π x - π (e₀ x) at hx
    change π (e₀ x + (c x).val) = π x
    rw [map_add, hx, add_comm, sub_add_cancel]
  · apply LinearMap.ext
    intro x
    change QF.mkQ (e₀ x + (c x).val) = g x
    rw [map_add]
    have hc0 : QF.mkQ (c x).val = 0 := by
      change (c x).val ∈ LinearMap.ker QF.mkQ
      rw [Submodule.ker_mkQ]
      exact (c x).property
    rw [hc0, add_zero]
    exact congrArg (fun f => f x) he₀

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
