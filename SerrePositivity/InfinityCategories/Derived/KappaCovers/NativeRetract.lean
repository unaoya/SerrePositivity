module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.HomotopyRetract
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.CompactStage
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-!
概要：同じ選択代表の実導来頂点の native retract を、同じ代表系の実頂点同型で被覆する。
方針：射影的二端点の局所化 Hom 計算で retract を K(D) に戻し、telescope 代表化を適用する。
規約：射影性なしに局所化射を持ち上げない。使われ方：D-8 d の covers の最後の段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 射影的二端点の主導来 retract は同じ K(D) の retract へ戻る。 -/
lemma dgProjective_homotopyRetract_of_derivedRetract {P M : ModuleCategory R D}
    (hP : moduleHomotopicallyProjective R D P) (hM : moduleHomotopicallyProjective R D M)
    (r : Retract ((moduleToDerived R D).obj P) ((moduleToDerived R D).obj M)) :
    Nonempty (Retract ((moduleToHomotopy R D).obj P) ((moduleToHomotopy R D).obj M)) := by
  let L := moduleHomotopyToDerivedClosed R D
  let s := (Retract.ofIso ((moduleToHomotopyDerivedIso R D).app P)).trans
    (r.trans (Retract.ofIso ((moduleToHomotopyDerivedIso R D).app M).symm))
  obtain ⟨i, hi⟩ := (moduleProjectiveLocalization_map_bijective R D hP
    ((moduleToHomotopy R D).obj M)).2 s.i
  obtain ⟨p, hp⟩ := (moduleProjectiveLocalization_map_bijective R D hM
    ((moduleToHomotopy R D).obj P)).2 s.r
  refine ⟨⟨i, p, ?_⟩⟩
  apply (moduleProjectiveLocalization_map_bijective R D hP
    ((moduleToHomotopy R D).obj P)).1
  rw [CategoryTheory.Functor.map_comp, hi, hp, s.retract, CategoryTheory.Functor.map_id]
  rfl

/-- 元の実導来圏内の retract は、同じ小さい代表集合の実加群で被覆できる。 -/
lemma dgKappaClosedProjectiveObjects_nativeRetractCovers {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    {y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌} {M : ModuleCategory R D}
    (hM : dgKappaClosedProjectiveObjects R D κ M)
    (r : F2.Idempotent.VertexRetraction y (dgConeModuleDerivedVertex R D M)) :
    ∃ N : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨P, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let P₀ := ForgetEnrichment.of (Complex R) P.val
  let H := dgModuleDerivedHoComparison R D
  have eP : H.obj (HomotopyCategory.mk (Simplex.vertex P)) ≅
      (moduleToDerived R D).obj P₀ := (moduleToHomotopyDerivedIso R D).app P₀
  let s := (Retract.ofIso eP.symm).trans ((r.map H).trans
    (Retract.ofIso (dgConeModuleDerivedVertex_classicalIso R D M)))
  obtain ⟨t⟩ := dgProjective_homotopyRetract_of_derivedRetract R D
    (dgSemifreeModule_isProjective R D P)
    (dgKappaClosedProjectiveObjects_projective R D κ M hM) s
  obtain ⟨N, hN, ⟨e⟩⟩ := dgKappaClosedProjectiveObjects_homotopyRetractCovers
    R D hκ hreg hM t
  refine ⟨N, hN, ⟨H.preimageIso (?_)⟩⟩
  exact dgConeModuleDerivedVertex_classicalIso R D N ≪≫
    ((moduleToHomotopyDerivedIso R D).app N).symm ≪≫
    (moduleHomotopyToDerivedClosed R D).mapIso e ≪≫
    (moduleToHomotopyDerivedIso R D).app P₀ ≪≫ eP.symm

end SerrePositivity.InfinityCategories
