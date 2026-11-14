module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRestrictionComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction

/-!
# BE の弱同値に沿う同じ制限と拡大の同値

概要：HA §4.2.3 の弱同値不変性を、指定した実制限へ接続する。
方針：同じ拡大の選択逆と指定制限を、native な右随伴の一意性で比較する。
規約：同値の逆は元の `strictModuleRestrict`。使われ方：全族の局所化への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
variable {A : Type u} [CommRing A]

/-- 概要：BE 弱同値の拡大は同じ制限を逆とする準圏同値（HA §4.2.3）。
方針：同じ拡大の二つの右随伴の全関手同型で両逆則を移す。
規約：指定の二関手を保持。使われ方：弱同値の反転と全族の降下。 -/
def strictModuleWeakEquivalence {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : QCatEquivalence (strictModuleInfinity A X) (strictModuleInfinity A Y) := by
  let e := (strictModuleExtend_weak f hf).choose
  have i : FunctorIso e.inv (strictModuleRestrict f) :=
    e.toAdjunction.rightAdjointFunctorIso (strictModuleAdjunction f)
  exact { hom := strictModuleExtend f
          inv := strictModuleRestrict f
          homInvIso := (i.precomp (strictModuleExtend f)).symm ≪≫ e.homInvIso
          invHomIso := (i.postcomp (strictModuleExtend f)).symm ≪≫ e.invHomIso }

/-- 概要：BE 弱同値に沿う指定制限も準圏同値（HA §4.2.3）。
方針：指定の二関手を持つ同値の逆を取る。
規約：元の出力解像度付き制限。使われ方：弱同値に沿う反変性。 -/
theorem strictModuleRestrict_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleRestrict f) :=
  (strictModuleWeakEquivalence f hf).symm.isQCatEquivalence

end SerrePositivity.EInfinity.BarrattEccles
