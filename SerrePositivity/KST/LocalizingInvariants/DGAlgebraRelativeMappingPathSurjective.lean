module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMappingPathQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathEndpointsSurjective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：底への合成 a≫p が次数全射なら、相対 mapping-path の target も次数全射である。
方針：指定終点の底を源へ持ち上げ、相対二端点と元の pullback に順に持ち上げる。
規約：斉次の存在だけを用い、線形切断や微分保存を仮定しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath
variable (R : Type u) [CommRing R] {C B W : Mon (Complex R)} (p : C ⟶ B) (a : W ⟶ C)

lemma gradedPullback (n : ℤ) : IsPullback ((inclusion R p a).hom.f n) ((projection R p a).hom.f n)
    ((RelativePath.source R p).hom.f n) (a.hom.f n) :=
  Functor.map_isPullback (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) n)
    (IsPullback.of_hasPullback (RelativePath.source R p).hom a.hom)

lemma target_surjective
    (hq : ∀ n : ℤ, Function.Surjective ((a ≫ p).hom.f n)) (n : ℤ) :
    Function.Surjective ((target R p a).hom.f n) := by
  intro y
  obtain ⟨w, hw⟩ := hq n (p.hom.f n y)
  change p.hom.f n (a.hom.f n w) = p.hom.f n y at hw
  obtain ⟨e, he₁, he₂⟩ := Types.exists_of_isPullback
    (Functor.map_isPullback (forget (ModuleCat.{u} R)) (RelativePath.gradedEndpointsPullback R p n))
    (a.hom.f n w) y hw
  change (RelativePath.endpointsSource R p).hom.f n e = a.hom.f n w at he₁
  change (RelativePath.endpointsTarget R p).hom.f n e = y at he₂
  obtain ⟨v, hv⟩ := RelativePath.endpointsMap_surjective R p n e
  have hs : (RelativePath.source R p).hom.f n v = a.hom.f n w := by
    have hn := congrArg (fun f => f.hom.f n) (RelativePath.endpointsMap_source R p)
    have hh := ConcreteCategory.congr_hom hn v
    change (RelativePath.endpointsSource R p).hom.f n
      ((RelativePath.endpointsMap R p).hom.f n v) = (RelativePath.source R p).hom.f n v at hh
    rw [hv, he₁] at hh
    exact hh.symm
  have ht : (RelativePath.target R p).hom.f n v = y := by
    have hn := congrArg (fun f => f.hom.f n) (RelativePath.endpointsMap_target R p)
    have hh := ConcreteCategory.congr_hom hn v
    change (RelativePath.endpointsTarget R p).hom.f n
      ((RelativePath.endpointsMap R p).hom.f n v) = (RelativePath.target R p).hom.f n v at hh
    rw [hv, he₂] at hh
    exact hh.symm
  obtain ⟨x, hx, _⟩ := Types.exists_of_isPullback
    (Functor.map_isPullback (forget (ModuleCat.{u} R)) (gradedPullback R p a n)) v w hs
  change (inclusion R p a).hom.f n x = v at hx
  refine ⟨x, ?_⟩
  change (RelativePath.target R p).hom.f n ((inclusion R p a).hom.f n x) = y
  rw [hx, ht]

lemma target_epi (hq : ∀ n : ℤ, Function.Surjective ((a ≫ p).hom.f n)) : Epi (target R p a).hom :=
  HomologicalComplex.epi_of_epi_f _
    (fun n => (ModuleCat.epi_iff_surjective _).2 (target_surjective R p a hq n))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeMappingPath
