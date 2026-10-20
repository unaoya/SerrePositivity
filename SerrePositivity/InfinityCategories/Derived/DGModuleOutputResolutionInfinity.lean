module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionNerve
/-!
概要：任意の dg 加群値関手の出力を、実分解 dg 圏を通じて半自由模型の実 ∞ 関手へ運ぶ。
方針：実入力射影の全 nerve 同値の逆と、実半自由出力射影の dg nerve を合成する。
規約：対象ごとの分解選択だけで済ませず、全単体上の関手と全関手比較同型を構成する。
使われ方：β5 の出力の射影性を仮定しない Hom の ∞ 関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 半自由出力の対象だけを共通宇宙へ上げた、同じ実出力 dg 射影。 -/
def dgModuleFunctorResolutionReplacementLift :
    DGFunctor R (DGModuleFunctorResolutionObject R C E F)
      (DGUniverseLift.{max (u + 1) w, v} (SemifreeDGModules R E)) :=
  (dgModuleFunctorResolutionReplacement R C E F).comp
    (dgUniverseLiftUp.{u, max (u + 1) w, v} R (SemifreeDGModules R E))
/-- 任意の dg 関手の実出力分解を、全単体を保持する半自由模型の ∞ 関手へ移す。 -/
def dgModuleOutputResolutionInfinity :
    dgNerve R (DGUniverseLift.{v, max (u + 1) w} C) ⟶
      dgNerve R (DGUniverseLift.{max (u + 1) w, v} (SemifreeDGModules R E)) :=
  (dgModuleFunctorResolutionSourceNerve_isQCatEquivalence R C E F).choose.inv ≫
    dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)
/-- 同じ実分解 dg 圏へ戻すと、構成した ∞ 関手は実半自由出力射影と全関手同型で一致する。 -/
def dgModuleOutputResolutionInfinity_comparisonIso :
    FunctorIso (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) ≫
      dgModuleOutputResolutionInfinity R C E F)
      (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)) := by
  have h := (dgModuleFunctorResolutionSourceNerve_isQCatEquivalence R C E F).choose.homInvIso
  have he := h.postcomp (dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F))
  change FunctorIso
    ((dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) ≫
      (dgModuleFunctorResolutionSourceNerve_isQCatEquivalence R C E F).choose.inv) ≫
      dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F))
    (𝟙 _ ≫ dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F)) at he
  simpa only [dgModuleOutputResolutionInfinity, Category.assoc, Category.id_comp] using he
end SerrePositivity.InfinityCategories
