module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMappingPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathSurjectiveSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection

/-!
概要：次数全射 p の上の相対 mapping-path は、元の源と絶対 mapping-path に準同型で写る。
方針：相対 source の split epi と準同型性を底変更し、元の源への比較から反映する。
規約：p 自身の準同型性は要求しない。使われ方：相対 class 模型の絶対模型への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath
variable (R : Type u) [CommRing R] {C B W : Mon (Complex R)} (p : C ⟶ B) (a : W ⟶ C)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n))

lemma relativeSource_epi : Epi (RelativePath.source R p).hom :=
  epi_of_epi_fac (congrArg Mon.Hom.hom (RelativePath.diagonal_source R p))

include hs in
lemma projection_quasiIso : QuasiIso (projection R p a).hom := by
  have := relativeSource_epi R p
  exact cochainPullback_snd_quasiIso (RelativePath.source R p).hom a.hom
    (RelativePath.source_quasiIso_of_surjective R p hs)

include hs in
lemma comparison_quasiIso : QuasiIso (comparison R p a).hom := by
  have := MappingPath.projection_quasiIso R a
  have hh : QuasiIso ((comparison R p a).hom ≫ (MappingPath.projection R a).hom) := by
    change QuasiIso ((comparison R p a ≫ MappingPath.projection R a).hom)
    rw [comparison_projection]
    exact projection_quasiIso R p a hs
  exact quasiIso_of_comp_right (comparison R p a).hom (MappingPath.projection R a).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath
