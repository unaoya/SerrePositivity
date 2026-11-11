module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleKappaCompactCone
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceCoproductComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HomotopyBinaryCoproduct
public import SerrePositivity.DifferentialGraded.Verdier.Derived
/-!
概要：同じ実導来加群頂点の κ-compact 性は二項直和で閉じる。
方針：零始点の実押し出しを作り、h 圏の余積比較で元の加群直和へ戻す。
規約：通常の compact 性を使わず、h 比較は指定頂点の同型にのみ使う。
使われ方：D-8 c4 の二項直和入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgModuleKappaCompact_binary {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M) (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M ⨿ N) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R D
  obtain ⟨S, hz, hx, hy, hS⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_zeroSourcePushoutSquare
    (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerived_pushout_isKappaCompact R D hκ S hS
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_of_isInitialVertex.{u, max (u+1) v} hκ.le hz.1) (hx ▸ hM) (hy ▸ hN)
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D
  let e : H.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex S 1 1) ≅ (moduleToDerived R D).obj (M ⨿ N) :=
    (H.mapIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroSourcePushoutCoproductIso S hS hz.1)).symm ≪≫
      (PreservesColimitPair.iso H _ _).symm ≪≫
      coprod.mapIso (eqToIso (congrArg H.obj (congrArg SSet.HomotopyCategory.mk hx)) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D M)
        (eqToIso (congrArg H.obj (congrArg SSet.HomotopyCategory.mk hy)) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D N) ≪≫
      PreservesColimitPair.iso (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D) M N
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso.{u, max (u+1) v}
    (H.preimageIso (e ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D (M ⨿ N)).symm))).mp hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
