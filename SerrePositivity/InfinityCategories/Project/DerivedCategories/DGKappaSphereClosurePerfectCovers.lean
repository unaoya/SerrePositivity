module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereClosureRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleHomotopyRangeClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeCover
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.NativeRetract
public import SerrePositivity.DifferentialGraded.Module.TensorFree

/-!
概要：sphere-only 閉包で有限 cell と perfect retract を同型まで被覆する。
方針：有限操作木を実閉包へ戻し、perfect の retract を telescope で分裂する。
規約：旧 perfect 小模型の対象を基底へ追加せず、同型までの被覆だけを結論する。
使われ方：D-2 の perfectCovers と、旧族から新族への被覆移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaSphereClosureObjects_finiteCellCovers {M : ModuleCategory R D}
    (hM : moduleFiniteCell R D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ) M := by
  obtain ⟨c⟩ := hM
  induction c with
  | zero =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_of_mem R D _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_zero R D hκ)
  | generator x hx =>
    obtain ⟨i, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule_covers R D PUnit.{u + 1}
      (fun _ => x) (fun _ => 0) (by simpa using (lt_trans Cardinal.one_lt_aleph0 hκ))
    let q := e ≪≫ coproductUniqueIso _ ≪≫ moduleTensorUnitIso R D (representable R x)
    exact ⟨_, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_sphereFree R D hκ i,
      ⟨(moduleToHomotopy R D).mapIso q⟩⟩
  | shift s c ih =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_shift R D _
      (fun M h s => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_shift R D hκ hreg M h s) ih s
  | @sum M N c d ihM ihN =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_of_iso R D _
      ((moduleToHomotopy R D).mapIso
        (moduleBiprodIso R D M N ≪≫ biprod.isoCoprod M N).symm)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_binary R D _
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_binaryClosed R D hκ hreg) ihM ihN)
  | cone c d f ihM ihN =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_cone R D _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_cone R D hκ hreg) ihM ihN f
  | iso c e ih =>
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyRange_of_iso R D _ ((moduleToHomotopy R D).mapIso e) ih

lemma dgKappaSphereClosureObjects_perfectHomotopyCovers (M : ModuleCategory R D)
    (hp : moduleHomotopicallyProjective R D M)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N ∧
      Nonempty ((moduleToHomotopy R D).obj N ≅ (moduleToHomotopy R D).obj M) := by
  obtain ⟨T, hT, ⟨r⟩⟩ := (modulePerfect_iff R D _).mp hM
  obtain ⟨P, hP, ⟨e⟩⟩ := dgKappaSphereClosureObjects_finiteCellCovers R D hκ hreg hT
  obtain ⟨r'⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgProjective_homotopyRetract_of_derivedRetract R D hp
    (moduleFiniteCellOver_homotopicallyProjective R D hT) r
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_homotopyRetractCovers R D hκ hreg hP
    (r'.trans (Retract.ofIso e.symm))

lemma dgKappaSphereClosureObjects_perfectCovers (M : ModuleCategory R D)
    (hM : modulePerfect R D ((moduleToDerived R D).obj M)) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ N ∧
      Nonempty ((moduleToDerived R D).obj N ≅ (moduleToDerived R D).obj M) := by
  let Q := moduleCanonicalProjectiveResolution R D M
  let eQ := moduleDerivedIso R D Q.π Q.quasiIso
  have hQ : modulePerfect R D ((moduleToDerived R D).obj Q.obj) :=
    (modulePerfect R D).prop_of_iso eQ.symm hM
  obtain ⟨N, hN, ⟨e⟩⟩ := dgKappaSphereClosureObjects_perfectHomotopyCovers
    R D hκ hreg Q.obj Q.projective hQ
  exact ⟨N, hN, ⟨((moduleToHomotopyDerivedIso R D).app N).symm ≪≫
    (moduleHomotopyToDerivedClosed R D).mapIso e ≪≫
    (moduleToHomotopyDerivedIso R D).app Q.obj ≪≫ eQ⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
