module
public import SerrePositivity.InfinityCategories.Derived.DGModuleVertexTriangles

/-! # K(D) の三角形の三対象を実 cofiber で表示する

概要：K(D) の distinguished triangle の三対象は実 cofiber 三角形の三対象と同型になる。
方針：標準 cone 表示を選び、通常の h と H⁰ の比較の単位を各対象で使う。
規約：第三射やシフトの自然性まで一致したとは主張しない。使われ方：対象条件の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の distinguished triangle の三対象は、実 cofiber 列の三対象で表示できる。 -/
lemma dgModuleTriangle_objectPresentation (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (ModuleHomotopyCategory A D)) :
    ∃ (t : ZeroTriangle (dgModuleNerve A D)) (_ : IsCofiberSequence t),
      Nonempty ((dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₁ ≅
        SSet.HomotopyCategory.mk (squareVertex t.square 0 0)) ∧
      Nonempty ((dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₂ ≅
        SSet.HomotopyCategory.mk (squareVertex t.square 1 0)) ∧
      Nonempty ((dgStableHomotopyEquivalence A (RightModule A D)).inverse.obj T.obj₃ ≅
        SSet.HomotopyCategory.mk (squareVertex t.square 1 1)) := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  let E := dgStableHomotopyEquivalence A (RightModule A D)
  refine ⟨dgModuleConeZeroTriangle A D f, dgModuleConeSquare_isPushout A D f, ?_, ?_, ?_⟩
  · refine ⟨E.inverse.mapIso (Triangle.π₁.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (Simplex.vertex (ForgetEnrichment.to (Complex A) M)))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (dgModuleConeSquare_vertex00 A D f)).symm
  · refine ⟨E.inverse.mapIso (Triangle.π₂.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (Simplex.vertex (ForgetEnrichment.to (Complex A) N)))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (dgModuleConeSquare_vertex10 A D f)).symm
  · refine ⟨E.inverse.mapIso (Triangle.π₃.mapIso e) ≪≫
      (E.unitIso.app (SSet.HomotopyCategory.mk
        (Simplex.vertex (ForgetEnrichment.to (Complex A) (moduleCone A D f))))).symm ≪≫ ?_⟩
    exact eqToIso (congrArg SSet.HomotopyCategory.mk (dgModuleConeSquare_vertex11 A D f)).symm

end SerrePositivity.InfinityCategories
