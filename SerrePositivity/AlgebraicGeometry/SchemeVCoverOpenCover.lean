module

public import SerrePositivity.AlgebraicGeometry.SchemeVCoverComposition
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Limits

/-!
概要：同型と開被覆の余積は、同じ付値環による v 判定を持つ。
方針：付値環の閉点の像を含む開へ、Spec 全体の写像を因子化する。
規約：開被覆・同型の法則。付値環の拡大は恒等射を使う。
使われ方：A07 の一般の始域を有限アフィン被覆で細分する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 同型は、同じ付値環への持ち上げで v 判定を持つ。 -/
theorem isSchemeVCover_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsSchemeVCover f := by
  intro V _ _ k
  refine ⟨V, inferInstance, inferInstance, RingHom.id V, k ≫ inv f,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, ?_⟩
  simp [Category.assoc]

/-- 開被覆の余積から元の空間への射は、同じ付値環のままで v 判定を持つ。 -/
theorem isSchemeVCover_sigmaDesc_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    [Small.{u} 𝒰.I₀] : IsSchemeVCover (Sigma.desc 𝒰.f) := by
  intro V _ _ k
  let i := 𝒰.idx (k (IsLocalRing.closedPoint V))
  have hrange : Set.range k ⊆ (𝒰.f i).opensRange := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map k.continuous).mem_open
      (𝒰.f i).opensRange.isOpen (𝒰.covers _)
  let l := IsOpenImmersion.lift (𝒰.f i) k hrange
  refine ⟨V, inferInstance, inferInstance, RingHom.id V, l ≫ Sigma.ι 𝒰.X i,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, ?_⟩
  rw [Category.assoc, Sigma.ι_comp_desc, IsOpenImmersion.lift_fac]
  simp

end SerrePositivity.AlgebraicGeometry
