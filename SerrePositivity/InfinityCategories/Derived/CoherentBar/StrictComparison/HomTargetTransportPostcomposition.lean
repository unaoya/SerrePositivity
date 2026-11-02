module
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomEndpointTransport
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison


/-!
概要：Hom の標的等号輸送を実等号射との後合成へ同定する。
方針：等号を消去し、同じ enriched Hom の単位則を使う。
規約：全次数の Hom 要素と実加群射を保持する。
使われ方：始点を保つ面の shift ブロックの端点輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarHomTargetTransport_post (M N N' : RightModule R D) (h : N = N') (q : ℤ)
    (z : (moduleHom R D M N).X q) :
    (dgModuleHomTargetTransport R D M N N' h q z).val =
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) M)
        (eqToHom (congrArg (ForgetEnrichment.of (Complex R)) h))).f q z := by
  cases h
  simp only [eqToHom_refl, eHomWhiskerLeft_id, HomologicalComplex.id_f, ModuleCat.id_apply]
  rfl

lemma dgBarModuleMorphismOfCycle_unit (M : RightModule R D) :
    moduleMorphismOfCycle R D (M := ForgetEnrichment.of (Complex R) M)
      (N := ForgetEnrichment.of (Complex R) M) (unitElement R M).val
        (unitElement R M).property = 𝟙 _ := by
  change (closedHomEquiv R (RightModule R D) _ _).symm
    ((closedHomEquiv R (RightModule R D) _ _) (𝟙 _)) = 𝟙 _
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.InfinityCategories
