module

public import SerrePositivity.AlgebraicGeometry.DenseOpenSpecialization
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverSpecializations
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
概要：稠密開の逆像のスキーム論的閉包は、v 判定を満たす射の基底全体へ全射。
方針：基底の特殊化の鎖を持ち上げ、その終点を開部分の像の閉包へ入れる。
規約：元の射の固有性は不要。開包含の準コンパクト性を明示する。
使われ方：Rydh 3.10 の狭義変換の全射性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
universe u

/-- 稠密開の逆像の像の構造射は、v 判定により全射。 -/
theorem surjective_openImage_of_vCover {X Y : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian Y] (f : X ⟶ Y) (hf : IsSchemeVCover f)
    (U : Y.Opens) (hU : Dense U.carrier) [QuasiCompact (f ⁻¹ᵁ U).ι] :
    Surjective ((f ⁻¹ᵁ U).ι.imageι ≫ f) := by
  constructor
  intro y
  obtain ⟨p, hp, hpy⟩ := exists_specialization_from_denseOpen Y U hU y
  obtain ⟨x, z, hxz, hxp, hzy⟩ := hf.liftsSpecializations hpy
  have hx : x ∈ f ⁻¹ᵁ U := by change f x ∈ U; rwa [hxp]
  have hxrange : x ∈ Set.range (f ⁻¹ᵁ U).ι := ⟨⟨x, hx⟩, rfl⟩
  have hz : z ∈ closure (Set.range (f ⁻¹ᵁ U).ι) :=
    closure_mono (Set.singleton_subset_iff.mpr hxrange) hxz.mem_closure
  have hr : Set.range (f ⁻¹ᵁ U).ι.imageι = closure (Set.range (f ⁻¹ᵁ U).ι) := by
    change Set.range (f ⁻¹ᵁ U).ι.ker.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  obtain ⟨w, hw⟩ := hr.symm ▸ hz
  exact ⟨w, by change f ((f ⁻¹ᵁ U).ι.imageι w) = y; rw [hw, hzy]⟩

end SerrePositivity.AlgebraicGeometry
