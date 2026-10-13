module

public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # スカラー錐の新しい座標そのものによる零ホモトピー

任意の複体 P に対し、Cone(a·id_P) 上では a 自身の作用が零ホモトピックとなる。
各次数の右成分 P^i を一つ前の次数の左成分 P^i へ送る明示的なホモトピーを使う。
複体の有界性、項の射影性、係数加群の有限性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits Preadditive HomologicalComplex HomologicalComplex.homotopyCofiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]

/-- スカラー錐の右成分を、一つ前の次数の左成分へ送るホモトピー成分。 -/
def scalarConeCoordinateHom (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
    ((scalarConeFunctor a).obj P).X i ⟶ ((scalarConeFunctor a).obj P).X j :=
  sndX (smulId a P) i ≫ inlX (smulId a P) i j hij

/-- 明示したホモトピー成分の dh+hd は、錐上の a 倍写像に一致する。 -/
theorem scalarConeCoordinate_nullHomotopicMap_eq (a : R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Homotopy.nullHomotopicMap' (scalarConeCoordinateHom a P) =
      smulId a ((scalarConeFunctor a).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (i - 1) i from by change i - 1 + 1 = i; omega)
    (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
  dsimp only [scalarConeCoordinateHom, scalarConeFunctor, CochainComplex.mappingCone]
  apply ext_from_X (smulId a P) (i + 1) i rfl
  · simp only [homotopyCofiber_d, comp_add, Category.assoc,
      d_sndX_assoc (a • 𝟙 P) i (i + 1) rfl,
      add_comp, comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp,
      add_zero, smulId, HomologicalComplex.smul_f_apply,
      HomologicalComplex.id_f, Linear.smul_comp,
      Linear.comp_smul, Category.comp_id]
    exact (Category.comp_id _).symm
  · simp only [homotopyCofiber_d, comp_add, Category.assoc,
      inrX_d_assoc, inrX_sndX_assoc,
      inlX_d (a • 𝟙 P) (i - 1) i (i + 1)
        (by change i - 1 + 1 = i; omega) rfl,
      comp_add, comp_neg, smulId, HomologicalComplex.smul_f_apply,
      HomologicalComplex.id_f, Linear.smul_comp, Category.id_comp,
      Linear.comp_smul, add_neg_cancel_left]
    exact (Category.comp_id _).symm

/-- Cone(a·id_P) 上の a 倍写像の明示的な零ホモトピー。指数を増やさない。 -/
def scalarConeCoordinateNullHomotopy (a : R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Homotopy (smulId a ((scalarConeFunctor a).obj P)) 0 :=
  (Homotopy.ofEq (scalarConeCoordinate_nullHomotopicMap_eq a P).symm).trans
    (Homotopy.nullHomotopy' (scalarConeCoordinateHom a P))

/-- スカラー錐の全次数のホモロジーを、新しい座標 a 自身が零化する。 -/
theorem scalarCone_coordinate_homology_smul_zero (a : R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (q : ℤ) :
    ∀ m : ((scalarConeFunctor a).obj P).homology q, a • m = 0 := by
  have h := (scalarConeCoordinateNullHomotopy a P).homologyMap_eq q
  rw [smulId, homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  intro m
  exact congrArg (fun f ↦ f.hom m) h

end SerrePositivity
