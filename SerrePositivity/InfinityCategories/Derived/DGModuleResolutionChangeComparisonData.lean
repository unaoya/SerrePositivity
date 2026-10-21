module
public import
  SerrePositivity.InfinityCategories.Derived.DGModuleResolutionChangeOutputComparisonNaturality
/-!
概要：元の指定分解変更比較を、同じ実二経路の前合成比較と入力変換へ同定する。
方針：恒等入力と二段前合成則を保ち、元の指定射の共役式を回収する。
規約：同値の逆と比較を選び直さない。使われ方：元の導来射作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
  (F G : DGFunctor R C (RightModule R E))
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, (F.comp (DGFunctor.id (RightModule R E))).map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    (G.comp (DGFunctor.id (RightModule R E))).map x y ≫
      eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
lemma dgModuleResolutionChangeIdentity_change_source_lift :
    (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (G.comp (DGFunctor.id
      (RightModule R E))))) = (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E (F.comp
      (DGFunctor.id (RightModule R E))))) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_sourceLift R C E
      (F := (F.comp (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule
        R E)))) a hs hq ha)
  simpa only [dgNerve.map_comp] using! h
lemma dgModuleResolutionChangeIdentity_change_output :
    (dgNerve.map (dgModuleResolutionChangeFunctor R C E (F := (F.comp (DGFunctor.id
      (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule R E)))) a hs hq ha)) ≫
      (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (G.comp (DGFunctor.id
      (RightModule R E))))) = (dgNerve.map (dgModuleFunctorResolutionReplacement R C E (F.comp
      (DGFunctor.id (RightModule R E))))) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgModuleResolutionChangeFunctor_replacement R C E
      (F := (F.comp (DGFunctor.id (RightModule R E)))) (G := (G.comp (DGFunctor.id (RightModule
        R E)))) a hs hq ha)
  simpa only [dgNerve.map_comp] using! h
end SerrePositivity.InfinityCategories
