module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionSourceDown
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationTriangle
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerComposition
/-!
概要：実分解比較を元の入力射影へ送ると、元の同じ射影の恒等射となる。
方針：実 fiber の射影の恒等性と、同じ宇宙比較・端点輸送を使う。
規約：元の指定同型と実切断を保持する。使われ方：kernel の指定余単位の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実分解比較を元の入力射影へ送った像は、Arrow として恒等。 -/
lemma dgModuleResolutionComparison_projection_arrow :
    Arrow.mk (((dgModuleFunctorResolutionSourceNerveEquivalence R C E F).homInvIso.postcomp
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F))).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (dgNerve.map (dgModuleFunctorResolutionSource R C E F))))) := by
  let := dgModuleFunctorResolutionSourceNerve_trivialKanFibration R C E F
  let T := DGModuleFunctorResolutionObject R C E F
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let L := dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)
  let D := dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C)
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  have h₀ := trivialKanEquivalence_homInvIso_projection_arrow L
  change Arrow.mk ((Q.homInvIso.postcomp L).hom) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex L))) at h₀
  let H := (hoFunctor.map ((ihom (dgNerve R T)).map D)).toFunctor
  have h₁ := congrArg H.mapArrow.obj h₀
  simp only [Functor.mapArrow_obj] at h₁
  have h₂ : Arrow.mk (((Q.homInvIso.postcomp L).postcomp D).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex (L ≫ D)))) := by
    rw [F2.functorIso_postcomp_hom]
    exact h₁
  rw [F2.functorIso_postcomp_postcomp] at h₂
  have hD : L ≫ D = P := by
    change dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) = _
    rw [← dgNerve.map_comp, dgModuleFunctorResolutionSourceLift_comp_down]
  have h₃ := congrArg (fun r :
      dgNerve R (DGModuleFunctorResolutionObject R C E F) ⟶ dgNerve R C ↦
    Arrow.mk (Q.homInvIso.postcomp r).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex r)))) hD
  exact Eq.mp h₃ h₂
end SerrePositivity.InfinityCategories
