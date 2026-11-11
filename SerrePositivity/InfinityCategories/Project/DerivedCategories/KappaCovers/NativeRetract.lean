module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.HomotopyRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.CompactStage
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 射影的二端点の主導来 retract は同じ K(D) の retract へ戻る。 -/
lemma dgProjective_homotopyRetract_of_derivedRetract {P M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (hP : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D P) (hM : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D M)
    (r : Retract ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj P) ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj M)) :
    Nonempty (Retract ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj P) ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj M)) := by
  let L := _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D
  let s := (Retract.ofIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app P)).trans
    (r.trans (Retract.ofIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app M).symm))
  obtain ⟨i, hi⟩ := (_root_.SerrePositivity.DifferentialGraded.moduleProjectiveLocalization_map_bijective R D hP
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj M)).2 s.i
  obtain ⟨p, hp⟩ := (_root_.SerrePositivity.DifferentialGraded.moduleProjectiveLocalization_map_bijective R D hM
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj P)).2 s.r
  refine ⟨⟨i, p, ?_⟩⟩
  apply (_root_.SerrePositivity.DifferentialGraded.moduleProjectiveLocalization_map_bijective R D hP
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R D).obj P)).1
  rw [CategoryTheory.Functor.map_comp, hi, hp, s.retract, CategoryTheory.Functor.map_id]
  rfl

/-- 元の実導来圏内の retract は、同じ小さい代表集合の実加群で被覆できる。 -/
lemma dgKappaClosedProjectiveObjects_nativeRetractCovers {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
    {y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌} {M : ModuleCategory R D}
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetraction y (dgConeModuleDerivedVertex R D M)) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨P, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let P₀ := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P.val
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D
  have eP : H.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) ≅
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj P₀ := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app P₀
  let s := (Retract.ofIso eP.symm).trans ((r.map H).trans
    (Retract.ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D M)))
  obtain ⟨t⟩ := dgProjective_homotopyRetract_of_derivedRetract R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_projective R D κ M hM) s
  obtain ⟨N, hN, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaClosedProjectiveObjects_homotopyRetractCovers
    R D hκ hreg hM t
  refine ⟨N, hN, ⟨H.preimageIso (?_)⟩⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D N ≪≫
    ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app N).symm ≪≫
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R D).mapIso e ≪≫
    (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app P₀ ≪≫ eP.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
