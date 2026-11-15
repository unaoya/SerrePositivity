module
public import SerrePositivity.HomologicalAlgebra.ProductTotal
public import Mathlib.Algebra.Homology.Single

/-!
概要：縦方向を次数零に集中させた二重複体の積全複体を、元の横複体へ戻す。
方針：同じ (q,0) 射影を前向きの射とし、他の縦次数の零性で逆射を作る。
規約：横複体は整数次数で非有界。積の完全性は仮定しない。
使われ方：HA 1.2.4、G10 の離散加群入力の複体比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory Limits Opposite
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]

/-- 縦次数零に集中させる二重複体の関手。 -/
def singleRowFunctor : CochainComplex C ℤ ⥤ HomologicalComplex₂ C (.up ℤ) (.up ℤ) :=
  (HomologicalComplex.single C (.up ℤ) 0).mapHomologicalComplex (.up ℤ)

variable {C}
/-- 指定された (q,0) 射影。 -/
def singleRowProjection (K : CochainComplex C ℤ) (q : ℤ) :
    ((singleRowFunctor C ⋙ functor C).obj K).X q ⟶ K.X q :=
  π ((singleRowFunctor C).obj K) q 0 q (by omega) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.X q)).hom

/-- 縦次数零の唯一の成分から積全次数へ戻す射。 -/
def singleRowLift (K : CochainComplex C ℤ) (q : ℤ) :
    K.X q ⟶ ((singleRowFunctor C ⋙ functor C).obj K).X q :=
  lift ((singleRowFunctor C).obj K) q (fun a b hab =>
    if hb : b = 0 then
      eqToHom (by congr 1; omega) ≫
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 (K.X a) b hb).inv
    else 0)

/-- 縦次数零の成分への射影と逆射は元の成分上で恒等。 -/
theorem singleRowLift_projection (K : CochainComplex C ℤ) (q : ℤ) :
    singleRowLift K q ≫ singleRowProjection K q = 𝟙 _ := by
  dsimp only [singleRowLift, singleRowProjection]
  rw [← Category.assoc, lift_π]
  simp [HomologicalComplex.singleObjXSelf]

/-- 唯一の非零縦成分を通る往復は、積全次数上でも恒等。 -/
theorem singleRowProjection_lift (K : CochainComplex C ℤ) (q : ℤ) :
    singleRowProjection K q ≫ singleRowLift K q = 𝟙 _ := by
  apply hom_ext ((singleRowFunctor C).obj K) q
  intro a b hab
  by_cases hb : b = 0
  · subst b
    have ha : a = q := by omega
    subst a
    simp [singleRowLift, singleRowProjection, Category.assoc,
      HomologicalComplex.singleObjXSelf]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (K.X a) b hb).eq_of_tgt _ _

/-- 指定射影を前向きの射とする、各全次数の同型。 -/
def singleRowDegreeIso (K : CochainComplex C ℤ) (q : ℤ) :
    ((singleRowFunctor C ⋙ functor C).obj K).X q ≅ K.X q where
  hom := singleRowProjection K q
  inv := singleRowLift K q
  hom_inv_id := singleRowProjection_lift K q
  inv_hom_id := singleRowLift_projection K q

/-- 指定射影は元の横微分と可換。縦微分は零である。 -/
theorem singleRowProjection_d (K : CochainComplex C ℤ) (q : ℤ) :
    ((singleRowFunctor C ⋙ functor C).obj K).d q (q + 1) ≫
        singleRowProjection K (q + 1) = singleRowProjection K q ≫ K.d q (q + 1) := by
  let L := (singleRowFunctor C).obj K
  have h := d_π L (q + 1) 0 q (by omega)
  have hz : (L.X (q + 1)).d (-1) 0 = 0 := rfl
  change ((functor C).obj L).d q (q + 1) ≫ π L (q + 1) 0 (q + 1) _ =
    π L (q + 1 - 1) 0 q _ ≫ (L.d (q + 1 - 1) (q + 1)).f 0 +
      (q + 1).negOnePow • (π L (q + 1) (-1) q _ ≫ (L.X (q + 1)).d (-1) 0) at h
  simp only [hz, comp_zero, smul_zero] at h
  have h := h.trans (add_zero _)
  have ht (r : ℤ) (hr : r = q) :
      π L r 0 q (by omega) ≫ (L.d r (q + 1)).f 0 =
        π L q 0 q (by omega) ≫ (L.d q (q + 1)).f 0 := by
    subst r
    rfl
  have hh := h.trans (ht (q + 1 - 1) (by omega))
  dsimp only [singleRowProjection]
  rw [← Category.assoc]
  erw [hh]
  rw [Category.assoc]
  change π L q 0 q _ ≫
      ((HomologicalComplex.single C (.up ℤ) 0).map (K.d q (q + 1))).f 0 ≫ _ = _
  rw [HomologicalComplex.single_map_f_self]
  simp [Category.assoc]
  rfl

/-- 同じ成分射影は元の複体の射と自然。 -/
theorem singleRowProjection_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (q : ℤ) :
    ((singleRowFunctor C ⋙ functor C).map f).f q ≫ singleRowProjection L q =
      singleRowProjection K q ≫ f.f q := by
  dsimp only [singleRowProjection, Functor.comp_map]
  rw [← Category.assoc, map_π, Category.assoc]
  change _ ≫ ((HomologicalComplex.single C (.up ℤ) 0).map (f.f q)).f 0 ≫ _ = _
  rw [HomologicalComplex.single_map_f_self]
  simp [Category.assoc]

/-- 同じ各次数の射影による複体の同型。 -/
def singleRowIso (K : CochainComplex C ℤ) :
    (singleRowFunctor C ⋙ functor C).obj K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (singleRowDegreeIso K) (fun i j hij => by
    have hj : i + 1 = j := hij
    subst j
    exact (singleRowProjection_d K i).symm)

variable (C)
/-- 縦次数零に集中させて積 total を取る操作は、元の複体関手と自然同型。 -/
def singleRowNatIso : singleRowFunctor C ⋙ functor C ≅ 𝟭 (CochainComplex C ℤ) :=
  NatIso.ofComponents singleRowIso (fun f => by
    ext q
    exact singleRowProjection_naturality f q)

end SerrePositivity.HomologicalAlgebra.ProductTotal
