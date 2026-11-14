module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Triangles.DGModuleVertexTriangles

/-! # K(D) の三角形の三対象を実 cofiber で表示する

概要：K(D) の distinguished triangle の三対象は実 cofiber 三角形の三対象と同型になる。
方針：標準 cone 表示を選び、通常の h と H⁰ の比較の単位を各対象で使う。
規約：第三射やシフトの自然性まで一致したとは主張しない。使われ方：対象条件の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- K(D) の distinguished triangle の三対象は、実 cofiber 列の三対象で表示できる。 -/
lemma dgModuleTriangle_objectPresentation (T : Triangle (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D)) :
    ∃ (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) (_ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t),
      Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₁ ≅
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)) ∧
      Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₂ ≅
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0)) ∧
      Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₃ ≅
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1)) := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f, ?_, ?_, ?_⟩
  · refine ⟨E.inverse.mapIso (Triangle.π₁.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) M)))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex00 A D f)).symm
  · refine ⟨E.inverse.mapIso (Triangle.π₂.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) N)))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex10 A D f)).symm
  · refine ⟨E.inverse.mapIso (Triangle.π₃.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) (moduleCone A D f))))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11 A D f)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
