module
public import SerrePositivity.DifferentialGraded.Module.Pretriangulated
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionTriangle

/-! # 全dg自然な合成cone比較によるK(D)の八面体公理 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleHomotopyIsTriangulated : IsTriangulated (ModuleHomotopyCategory A D) :=
  IsTriangulated.mk' (by
    rintro ⟨M : ModuleCategory A D⟩ ⟨N : ModuleCategory A D⟩ ⟨P : ModuleCategory A D⟩ f' g'
    let Q := moduleToHomotopy A D
    obtain ⟨f, rfl⟩ := Q.map_surjective f'
    obtain ⟨g, rfl⟩ := Q.map_surjective g'
    refine ⟨Q.obj M, Q.obj N, Q.obj P, Q.obj (moduleCone A D f), Q.obj (moduleCone A D g),
      Q.obj (moduleCone A D (f ≫ g)), Q.map f, Q.map g,
      Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
      _, _, moduleHomotopyConeTriangle_distinguished A D f,
      _, _, moduleHomotopyConeTriangle_distinguished A D g,
      _, _, moduleHomotopyConeTriangle_distinguished A D (f ≫ g), ⟨?_⟩⟩
    let α := moduleConeTriangleMap A D f (f ≫ g) (𝟙 M) g (by rw [Category.id_comp])
    let β := moduleConeTriangleMap A D (f ≫ g) g f (𝟙 P) (by rw [Category.comp_id])
    refine Triangulated.Octahedron.mk (Q.map α.hom₃) (Q.map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact (Q.mapTriangle.map α).comm₂
    · exact (Q.mapTriangle.map α).comm₃.symm.trans (by
        change (Q.map (moduleConeConnecting A D f) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M) ≫
          (Q.map (𝟙 M))⟦(1 : ℤ)⟧' = _
        rw [Q.map_id M, (shiftFunctor (ModuleHomotopyCategory A D) (1 : ℤ)).map_id (Q.obj M)]
        exact Category.comp_id _)
    · exact (Q.mapTriangle.map β).comm₂.trans (by
        change Q.map (𝟙 P) ≫ Q.map (moduleConeInr A D g) = Q.map (moduleConeInr A D g)
        rw [Q.map_id P]
        exact Category.id_comp _)
    · exact (Q.mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (moduleHomotopyConeCompTriangle_distinguished A D f g) _ ?_
      change Triangle.mk (Q.map (moduleConeCompMap A D f g))
        (Q.map (moduleConeCompSecondMap A D f g))
        ((moduleHomotopyConeTriangle A D g).mor₃ ≫
          (moduleHomotopyConeTriangle A D f).mor₂⟦(1 : ℤ)⟧') ≅
            moduleHomotopyConeCompTriangle A D f g
      exact eqToIso (congrArg (fun c => Triangle.mk (Q.map (moduleConeCompMap A D f g))
        (Q.map (moduleConeCompSecondMap A D f g)) c) (moduleHomotopyConeComp_mor₃ A D f g).symm))

end SerrePositivity.DifferentialGraded
