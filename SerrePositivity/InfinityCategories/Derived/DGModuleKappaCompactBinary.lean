module
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactCone
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceCoproductComparison
public import SerrePositivity.InfinityCategories.Stable.HomotopyBinaryCoproduct
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgModuleKappaCompact_binary {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) {M N : ModuleCategory R D}
    (hM : dgModuleKappaCompact R D κ M) (hN : dgModuleKappaCompact R D κ N) :
    dgModuleKappaCompact R D κ (M ⨿ N) := by
  letI := dgModuleDerivedInfinityCategory_isStable R D
  obtain ⟨S, hz, hx, hy, hS⟩ := exists_zeroSourcePushoutSquare
    (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N)
  have hc := dgModuleDerived_pushout_isKappaCompact R D hκ S hS
    (F2.Compact.isKappaCompact_of_isInitialVertex.{u, max (u+1) v} hκ.le hz.1) (hx ▸ hM) (hy ▸ hN)
  let H := dgModuleDerivedHoComparison R D
  let e : H.obj (squareHoVertex S 1 1) ≅ (moduleToDerived R D).obj (M ⨿ N) :=
    (H.mapIso (zeroSourcePushoutCoproductIso S hS hz.1)).symm ≪≫
      (PreservesColimitPair.iso H _ _).symm ≪≫
      coprod.mapIso (eqToIso (congrArg H.obj (congrArg SSet.HomotopyCategory.mk hx)) ≪≫
        dgConeModuleDerivedVertex_classicalIso R D M)
        (eqToIso (congrArg H.obj (congrArg SSet.HomotopyCategory.mk hy)) ≪≫
        dgConeModuleDerivedVertex_classicalIso R D N) ≪≫
      PreservesColimitPair.iso (moduleToDerived R D) M N
  exact (F2.Compact.isKappaCompact_iff_of_iso.{u, max (u+1) v}
    (H.preimageIso (e ≪≫ (dgConeModuleDerivedVertex_classicalIso R D (M ⨿ N)).symm))).mp hc

end SerrePositivity.InfinityCategories
