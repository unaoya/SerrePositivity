module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule

/-!
概要：KST §5、Stacks 0815 の境界ねじれと係数局所化の所属判定。
方針：境界元の冪と局所化の分母の二つを順に払う。
規約：Noether 条件や境界元の正則性を仮定しない。
使われ方：純変換の係数局所化との可換性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/--
概要：局所化先の境界ねじれへの所属は元の加群で分母倍が境界ねじれとなることと同値。
方針：冪消滅と局所化写像の核の分母消滅を交換する。
規約：KST §5、Stacks 0815、分母は一般の部分モノイドの元。
使われ方：純変換の商写像の局所化の核の条件。
-/
theorem localized_mem_boundaryTorsion_iff (S : Submonoid R) (f : R)
    (η : M →ₗ[R] N) [IsLocalizedModule S η] (m : M) :
    η m ∈ boundaryTorsion f N ↔ ∃ s : S, s.val • m ∈ boundaryTorsion f M := by
  constructor
  · intro hm
    obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f N _).mp hm
    have hη : η (f ^ n • m) = 0 := by rw [η.map_smul, hn]
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S η).mp hη
    refine ⟨s, (mem_boundaryTorsion_iff f M _).mpr ⟨n, ?_⟩⟩
    exact (smul_comm _ _ _).trans hs
  · rintro ⟨s, hs⟩
    obtain ⟨n, hn⟩ := (mem_boundaryTorsion_iff f M _).mp hs
    apply (mem_boundaryTorsion_iff f N _).mpr
    refine ⟨n, ?_⟩
    apply IsLocalizedModule.smul_injective η s
    change s.val • (f ^ n • η m) = s.val • (0 : N)
    rw [smul_zero, smul_comm, ← η.map_smul, ← η.map_smul, hn, η.map_zero]

/--
概要：境界ねじれの所属は係数環を拡大して境界元をその像に置き換えても一致する。
方針：同じ冪消滅判定を代数写像とスカラー作用の両立で比較する。
規約：KST §5、Stacks 0815、加群には係数環拡大の作用を指定する。
使われ方：局所化先の純変換を局所化された環上の商として扱う。
-/
theorem mem_boundaryTorsion_algebraMap_iff {A : Type*} [CommRing A] [Algebra R A]
    [Module A N] [IsScalarTower R A N] (f : R) (n : N) :
    n ∈ boundaryTorsion (algebraMap R A f) N ↔ n ∈ boundaryTorsion f N := by
  rw [mem_boundaryTorsion_iff, mem_boundaryTorsion_iff]
  simp only [← map_pow, algebraMap_smul]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
