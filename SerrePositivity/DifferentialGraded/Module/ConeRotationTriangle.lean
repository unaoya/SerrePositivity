module
public import SerrePositivity.DifferentialGraded.Module.ConeRotationHomotopy
public import SerrePositivity.DifferentialGraded.Module.DistinguishedTriangles

/-! # K(D)の標準cone三角形の回転同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

@[reassoc] lemma moduleConeRotation_connecting_homotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleToHomotopy A D).map (moduleConeConnecting A D f) ≫
      (moduleToHomotopy A D).map (moduleConeRotationHom A D f) =
        (moduleToHomotopy A D).map (moduleConeInr A D (moduleConeInr A D f)) := by
  rw [← CategoryTheory.Functor.map_comp]
  exact (moduleToHomotopy_map_eq_iff A D _ _).2 ⟨moduleConeRotationConnectingHomotopy A D f⟩

/-- 標準cone三角形の回転は、その右包含の標準cone三角形と同型。 -/
def moduleHomotopyConeRotationIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHomotopyConeTriangle A D f).rotate ≅
      moduleHomotopyConeTriangle A D (moduleConeInr A D f) := by
  let Q := moduleToHomotopy A D
  refine Triangle.isoMk ((moduleHomotopyConeTriangle A D f).rotate)
    (moduleHomotopyConeTriangle A D (moduleConeInr A D f))
    (Iso.refl (Q.obj N)) (Iso.refl (Q.obj (moduleCone A D f)))
    (moduleConeRotationShiftIso A D f) ?_ ?_ ?_
  · change Q.map (moduleConeInr A D f) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (moduleConeInr A D f)
    rw [Category.comp_id, Category.id_comp]
  · change (Q.map (moduleConeConnecting A D f) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M) ≫
      ((Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (moduleConeRotationHom A D f)) =
        𝟙 _ ≫ Q.map (moduleConeInr A D (moduleConeInr A D f))
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, Category.id_comp]
    exact moduleConeRotation_connecting_homotopy A D f
  · change (-(Q.map f)⟦(1 : ℤ)⟧') ≫ (𝟙 (Q.obj N))⟦(1 : ℤ)⟧' =
      ((Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (moduleConeRotationHom A D f)) ≫
        (Q.map (moduleConeConnecting A D (moduleConeInr A D f)) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app N)
    rw [(shiftFunctor (ModuleHomotopyCategory A D) (1 : ℤ)).map_id, Category.comp_id]
    have hn := (Q.commShiftIso (1 : ℤ)).hom.naturality f
    change Q.map (f⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app N =
      (Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map f)⟦(1 : ℤ)⟧' at hn
    symm
    calc
      _ = (Q.commShiftIso (1 : ℤ)).inv.app M ≫
          Q.map (moduleConeRotationHom A D f ≫
            moduleConeConnecting A D (moduleConeInr A D f)) ≫
              (Q.commShiftIso (1 : ℤ)).hom.app N := by
        simp only [Q.map_comp, Category.assoc]
      _ = (Q.commShiftIso (1 : ℤ)).inv.app M ≫ Q.map (-f⟦(1 : ℤ)⟧') ≫
          (Q.commShiftIso (1 : ℤ)).hom.app N := by rw [moduleConeRotation_connecting]
      _ = -((Q.commShiftIso (1 : ℤ)).inv.app M ≫
          (Q.map (f⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app N)) := by
        rw [Q.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
      _ = -((Q.commShiftIso (1 : ℤ)).inv.app M ≫
          ((Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map f)⟦(1 : ℤ)⟧')) :=
        congrArg (fun a => -((Q.commShiftIso (1 : ℤ)).inv.app M ≫ a)) hn
      _ = -(Q.map f)⟦(1 : ℤ)⟧' := by rw [Iso.inv_hom_id_app_assoc]

lemma moduleDistinguished_rotate (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.rotate ∈ moduleDistinguishedTriangles A D := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  exact ⟨N, moduleCone A D f, moduleConeInr A D f,
    ⟨(rotate _).mapIso e ≪≫ moduleHomotopyConeRotationIso A D f⟩⟩


@[reassoc] lemma moduleDistinguished_comp_zero₂₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₂ ≫ T.mor₃ = 0 := by
  have h := moduleDistinguished_comp_zero₁₂ A D T.rotate (moduleDistinguished_rotate A D T hT)
  exact h

@[reassoc] lemma moduleDistinguished_comp_zero₃₁
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
  have h := moduleDistinguished_comp_zero₂₃ A D T.rotate (moduleDistinguished_rotate A D T hT)
  change T.mor₃ ≫ (-T.mor₁⟦(1 : ℤ)⟧') = 0 at h
  rw [Preadditive.comp_neg, neg_eq_zero] at h
  exact h

end SerrePositivity.DifferentialGraded
