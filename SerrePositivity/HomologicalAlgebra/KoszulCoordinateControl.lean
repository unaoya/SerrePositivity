module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl

/-! # Koszul 複体の座標そのものによる零ホモトピー

任意の複体 P に対し、Cone(a·id_P) 上では a 自身の作用が零ホモトピックとなる。
各次数の右成分 P^i を一つ前の次数の左成分 P^i へ送る明示的なホモトピーを使う。
複体の有界性、項の射影性、係数加群の有限性は要求しない。
既存のスカラー零ホモトピーを次の錐へ持ち上げ、Koszul の各座標を指数 1 で制御する。
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

/-- スカラーの零ホモトピーの、指定した隣接次数における dh+hd の式。 -/
theorem scalarNullHomotopy_component {a : R}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : Homotopy (smulId a P) 0)
    (i j k : ℤ) (hji : (ComplexShape.up ℤ).Rel j i)
    (hik : (ComplexShape.up ℤ).Rel i k) :
    P.d i k ≫ h.hom k i + h.hom i j ≫ P.d j i = a • 𝟙 (P.X i) := by
  have hc := h.comm i
  rw [dNext_eq h.hom hik, prevD_eq h.hom hji, HomologicalComplex.zero_f_apply,
    add_zero] at hc
  simpa only [smulId, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f] using hc.symm

/-- 錐の左側では符号を反転し、右側では元のホモトピーを使う。 -/
def scalarConeLiftHom {a : R} (b : R)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : Homotopy (smulId a P) 0)
    (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel j i) :
    (HomologicalComplex.homotopyCofiber (smulId b P)).X i ⟶
      (HomologicalComplex.homotopyCofiber (smulId b P)).X j :=
  -(fstX (smulId b P) i (i + 1) rfl ≫ h.hom (i + 1) i ≫
    inlX (smulId b P) i j _hij) +
    sndX (smulId b P) i ≫ h.hom i j ≫ inrX (smulId b P) j

/-- 持ち上げたホモトピー成分の dh+hd は、錐上の元のスカラー作用に一致する。 -/
theorem scalarConeLift_nullHomotopicMap_eq {a : R} (b : R)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : Homotopy (smulId a P) 0) :
    Homotopy.nullHomotopicMap' (scalarConeLiftHom b h) =
      smulId a (HomologicalComplex.homotopyCofiber (smulId b P)) := by
  have hs (r : R) (l : ℤ) : (smulId r P).f l = r • 𝟙 (P.X l) := rfl
  have hsC (l : ℤ) : (smulId a (HomologicalComplex.homotopyCofiber (smulId b P))).f l =
      a • 𝟙 ((HomologicalComplex.homotopyCofiber (smulId b P)).X l) := rfl
  apply HomologicalComplex.Hom.ext
  funext i
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (i - 1) i from by change i - 1 + 1 = i; omega)
    (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
  dsimp only [scalarConeLiftHom]
  apply ext_from_X (smulId b P) (i + 1) i rfl
  · simp only [homotopyCofiber_d, comp_add, comp_neg, add_comp, neg_comp, Category.assoc,
      inlX_d_assoc (smulId b P) i (i + 1) (i + 1 + 1) rfl rfl,
      inlX_d (smulId b P) (i - 1) i (i + 1)
        (by change i - 1 + 1 = i; omega) rfl,
      inlX_fstX_assoc, inlX_sndX_assoc, inrX_fstX_assoc, inrX_sndX_assoc,
      zero_comp, comp_zero, zero_add, add_zero, neg_zero, smul_zero, neg_neg, Category.id_comp,
      hs, hsC, Linear.smul_comp, Linear.comp_smul]
    calc
      _ = (P.d (i + 1) (i + 1 + 1) ≫ h.hom (i + 1 + 1) (i + 1) +
          h.hom (i + 1) i ≫ P.d i (i + 1)) ≫ inlX (smulId b P) (i + 1) i rfl := by
        simp only [add_comp]
        abel
      _ = _ := by
        rw [scalarNullHomotopy_component h (i + 1) i (i + 1 + 1) rfl rfl]
        simp only [Linear.smul_comp, Category.id_comp]
        exact (Category.comp_id _).symm
  · simp only [homotopyCofiber_d, comp_add, comp_neg, add_comp, neg_comp, Category.assoc,
      inrX_d, inrX_d_assoc, inrX_fstX_assoc, inrX_sndX_assoc,
      zero_comp, comp_zero, zero_add, neg_zero, hsC, Linear.comp_smul]
    calc
      _ = (P.d i (i + 1) ≫ h.hom (i + 1) i + h.hom i (i - 1) ≫ P.d (i - 1) i) ≫
          inrX (smulId b P) i := by simp only [add_comp, Category.assoc]
      _ = _ := by
        rw [scalarNullHomotopy_component h i (i - 1) (i + 1)
          (by change i - 1 + 1 = i; omega) rfl]
        simp only [Linear.smul_comp, Category.id_comp]
        exact (Category.comp_id _).symm

/-- P 上のスカラー零ホモトピーは、別のスカラー b の錐へ指数を変えずに持ち上がる。 -/
def scalarConeLiftNullHomotopy {a : R} (b : R)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (h : Homotopy (smulId a P) 0) :
    Homotopy (smulId a ((scalarConeFunctor b).obj P)) 0 :=
  (Homotopy.ofEq (scalarConeLift_nullHomotopicMap_eq b h).symm).trans
    (Homotopy.nullHomotopy' (scalarConeLiftHom b h))

/-- 複体を係数とする Koszul 構成では、各座標自身の作用が零ホモトピックである。 -/
def koszulCoordinateNullHomotopy {e : ℕ} (z : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin e) :
    Homotopy (smulId (z j) ((koszulFunctor z).obj P)) 0 := by
  induction e with
  | zero => exact Fin.elim0 j
  | succ e ih =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · exact scalarConeCoordinateNullHomotopy (z (Fin.last e))
        ((koszulFunctor (Fin.init z)).obj P)
    · exact scalarConeLiftNullHomotopy (z (Fin.last e)) (ih (Fin.init z) j)

/-- 任意の係数加群の Koszul ホモロジーを、各座標自身が全次数で零化する。 -/
theorem koszulModuleHomology_coordinate_smul_zero {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (j : Fin e) (q : ℤ) :
    ∀ m : ((koszulModuleFunctor z).obj M).homology q, z j • m = 0 := by
  have h := (koszulCoordinateNullHomotopy z
    ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M) j).homologyMap_eq q
  rw [smulId, homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  intro m
  exact congrArg (fun f ↦ f.hom m) h

/-- 列の生成イデアルは、任意の係数加群の全次数の Koszul ホモロジーを零化する。 -/
theorem span_le_annihilator_koszulModuleHomology {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (q : ℤ) :
    Ideal.span (Set.range z) ≤
      Module.annihilator R (((koszulModuleFunctor z).obj M).homology q) := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact Module.mem_annihilator.mpr (koszulModuleHomology_coordinate_smul_zero z M j q)

end SerrePositivity
