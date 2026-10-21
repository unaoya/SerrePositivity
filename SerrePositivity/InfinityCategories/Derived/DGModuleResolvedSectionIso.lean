module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSourceSection
/-!
概要：元の出力分解の実入力射影と指定切断の逆順合成を、恒等全関手へ比較する。
方針：同じ nerve 同値の homInvIso と、対象宇宙の持ち上げの実等式を使う。
規約：同じ指定逆を保持する。使われ方：一般 kernel の実右随伴と余単位の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ入力射影と実切断の逆順合成の全関手同型。 -/
def dgModuleResolvedProjectionSectionIso :
    FunctorIso (dgNerve.map (dgModuleFunctorResolutionSource R C E F) ≫
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)) (𝟙 _) := by
  have e := (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).homInvIso
  change FunctorIso (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) ≫
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) (𝟙 _) at e
  simpa only [dgModuleFunctorResolutionSourceLift, dgNerve.map_comp, Category.assoc] using e
end SerrePositivity.InfinityCategories
