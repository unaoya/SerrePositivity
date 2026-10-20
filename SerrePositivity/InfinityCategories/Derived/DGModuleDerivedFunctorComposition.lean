module
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedFunctor
/-!
概要：半自由模型上の実導来関手の恒等と合成を、全関手同型で比較する。
方針：射影的模型の厳密な dg 関手の恒等・合成と、同じ比較同値の余単位を使う。
規約：高次随伴・全 coherence は別工程。使われ方：β5 の tensor の単位・合成の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E T : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
variable [DGCategory R T] [Small.{u} T]
omit [DGCategory R E] [Small.{u} E] [DGCategory R T] [Small.{u} T] in
/-- 恒等 dg 関手からの実導来関手は、全関手圏で恒等と同型。 -/
def dgModuleDerivedFunctor_id_iso :
    FunctorIso (dgModuleDerivedFunctor R D D (DGFunctor.id (RightModule R D)) (fun _ h => h))
      (𝟙 (dgModuleDerivedInfinityCategory R D)) := by
  have hd : dgProjectiveModuleFunctor R D D (DGFunctor.id (RightModule R D)) (fun _ h => h) =
      DGFunctor.id (ProjectiveDGModules R D) :=
    dgFullFunctorRestriction_id R (RightModule R D) (dgModuleProjectiveProperty R D)
  rw [dgModuleDerivedFunctor, hd, dgNerve.map_id, Category.id_comp]
  exact (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.homInvIso
/-- 実導来関手の合成は、同じ二つの元の dg 関手の合成の実導来関手と全関手圏で同型。 -/
def dgModuleDerivedFunctor_comp_iso
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (G : DGFunctor R (RightModule R E) (RightModule R T))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M))
    (hG : ∀ M, dgModuleProjectiveProperty R E M → dgModuleProjectiveProperty R T (G.obj M)) :
    FunctorIso (dgModuleDerivedFunctor R D E F hF ≫ dgModuleDerivedFunctor R E T G hG)
      (dgModuleDerivedFunctor R D T (F.comp G) (fun M hM => hG _ (hF M hM))) := by
  have hd : dgProjectiveModuleFunctor R D T (F.comp G) (fun M hM => hG _ (hF M hM)) =
      (dgProjectiveModuleFunctor R D E F hF).comp (dgProjectiveModuleFunctor R E T G hG) :=
    dgFullFunctorRestriction_comp R (RightModule R D) (RightModule R E) F G _ _ _ hF hG
  have h₀ := (dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.invHomIso.precomp
    (dgNerve.map (dgSemifreeToProjective R D) ≫
      dgNerve.map (dgProjectiveModuleFunctor R D E F hF))
  have h := h₀.postcomp (dgNerve.map (dgProjectiveModuleFunctor R E T G hG) ≫
      (dgSemifreeToProjectiveNerve_isQCatEquivalence R T).choose.inv)
  simpa only [dgModuleDerivedFunctor, hd, dgNerve.map_comp, Category.assoc,
    Category.comp_id] using! h
end SerrePositivity.InfinityCategories
