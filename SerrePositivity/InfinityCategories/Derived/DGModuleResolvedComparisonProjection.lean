module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionComparisonProjection
public import SerrePositivity.InfinityCategories.Stable.FunctorIsoArrowTransport
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSectionIso
/-!
概要：元の入力切断の同じ比較同型の底への像を、端点輸送も含めて回収する。
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
/-- 元の入力比較同型は、同じ分解 nerve 同値の指定比較と HEq。 -/
lemma dgModuleResolvedProjectionSectionIso_heq :
    HEq (dgModuleResolvedProjectionSectionIso R C E F)
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).homInvIso := by
  unfold dgModuleResolvedProjectionSectionIso
  dsimp only [_root_.id]
  simp only [eq_mp_eq_cast, cast_heq]
/-- 元の入力射影と指定切断の同じ比較は、入力射影で恒等となる。 -/
lemma dgModuleResolvedProjectionSectionIso_projection_arrow :
    Arrow.mk ((dgModuleResolvedProjectionSectionIso R C E F).postcomp
      (dgNerve.map (dgModuleFunctorResolutionSource R C E F))).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
        (dgNerve.map (dgModuleFunctorResolutionSource R C E F))))) := by
  let Q := dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let P := dgNerve.map (dgModuleFunctorResolutionSource R C E F)
  let U := dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let a := dgModuleResolvedProjectionSectionIso R C E F
  have hf : Q.hom ≫ Q.inv = P ≫ (U ≫ Q.inv) := by
    change dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) ≫ Q.inv = _
    rw [dgModuleFunctorResolutionSourceLift, dgNerve.map_comp, Category.assoc]
  have hh := F2.functorIso_postcomp_heq_of_heq Q.homInvIso a hf rfl
    (dgModuleResolvedProjectionSectionIso_heq R C E F) P
  have ha := functorIso_hom_arrow_of_heq (a.postcomp P) (Q.homInvIso.postcomp P)
    (congrArg (fun f ↦ f ≫ P) hf.symm) rfl hh
  exact ha.trans (dgModuleResolutionComparison_projection_arrow R C E F)
end SerrePositivity.InfinityCategories
