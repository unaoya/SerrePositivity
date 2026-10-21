module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionStrictNatTransInvertible
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso
/-!
概要：同じ双加群射の像と準同型性を、実分解後の可逆性へ接続する。
方針：元の評価射・全 Hom 自然性・型付きの射の一致を保持する。
規約：出力の射影性と原 Hom の平坦性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso
    (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
    (C : Type (max (u + 1) v)) [DGCategory R C]
    {P Q : BimoduleCategory R E C} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E C f) :
    IsIso (functorHomPostcomp
      (dgNerve.map (BimoduleCategory.underlying R E C P).toFunctor)
      (dgNerve.map (BimoduleCategory.underlying R E C Q).toFunctor)
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      ((dgBimoduleFunctorHomFunctor R E C).map f)) := by
  exact dgModuleResolution_strictNatTrans_isIso_of_quasiIso R C E f.val f.property
    (fun x => BimoduleCategory.quasiIso_evaluation R E C hf x)
end
end SerrePositivity.InfinityCategories
