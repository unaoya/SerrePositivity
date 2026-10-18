module

public import SerrePositivity.KST.DerivedGeometry.LinearComplexCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
概要：写像複体の cone 比較と標準三角形の射との両立を証明する。
方針：二成分の表示を使い、標準包含と connecting map を比較する。
規約：cone の代表可能性だけで三角形の両立を仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の導来局所化の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
variable [HasBinaryBiproducts C]

/--
概要：写像複体の cone 比較は標準包含を保つ。
方針：cone の第一成分が零、第二成分が元の cochain となることを使う。
規約：実際の標準包含と同じ後合成射を比較する。
使われ方：Drinfeld §2.4、KST D4 の標準三角形の比較。
-/
theorem mappingConeComparison_inr (T : CochainComplex C ℤ)
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    mappingCone.inr (mappingPostcompose A T f) ≫ mappingConeComparison A T f =
      mappingPostcompose A T (mappingCone.inr f) := by
  ext q a
  change mappingCone.liftCochain f
    ((mappingCone.fst (mappingPostcompose A T f)).val.v q (q + 1) rfl
      ((mappingCone.inr (mappingPostcompose A T f)).f q a))
    ((mappingCone.snd (mappingPostcompose A T f)).v q q (add_zero q)
      ((mappingCone.inr (mappingPostcompose A T f)).f q a)) rfl =
    a.comp (Cochain.ofHom (mappingCone.inr f)) (add_zero q)
  have h₁ : (mappingCone.fst (mappingPostcompose A T f)).val.v q (q + 1) rfl
      ((mappingCone.inr (mappingPostcompose A T f)).f q a) = 0 := by
    rw [← ModuleCat.comp_apply, mappingCone.inr_f_fst_v]
    rfl
  have h₂ : (mappingCone.snd (mappingPostcompose A T f)).v q q (add_zero q)
      ((mappingCone.inr (mappingPostcompose A T f)).f q a) = a := by
    rw [← ModuleCat.comp_apply, mappingCone.inr_f_snd_v]
    rfl
  exact (congrArg₂ (fun b c => mappingCone.liftCochain f b c rfl) h₁ h₂).trans (by
    simp [mappingCone.liftCochain])

/--
概要：一般の加法圏の cone の connecting map は shift した第一射影の負。
方針：cone の二つの包含との合成で射を比較する。
規約：Mathlib の標準三角形の符号を保持する。
使われ方：Drinfeld §2.4、KST D4 の標準三角形の比較。
-/
theorem coneConnecting_component {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n =
      -((mappingCone.fst f).val.v n (n + 1) rfl ≫
        (X.shiftFunctorObjXIso 1 n (n + 1) rfl).inv) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · simp only [mappingCone.inl_v_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inl_v_fst_v_assoc]
  · simp only [mappingCone.inr_f_triangle_mor₃_f, Preadditive.comp_neg,
      mappingCone.inr_f_fst_v_assoc, zero_comp, neg_zero]

/--
概要：cochain の標的次数の同一視を射の合成として計算する。
方針：二つの標的次数が等しいことを次数条件から導き、等式で帰納する。
規約：依存した射の族の成分を暗黙の書換えで同一視しない。
使われ方：Drinfeld §2.4、KST D4 の cone と shift の次数の比較。
-/
theorem cochain_component_transport {T X : CochainComplex C ℤ} {q : ℤ}
    (a : Cochain T X q) (p r r' : ℤ) (h : p + q = r) (h' : p + q = r') :
    a.v p r h = a.v p r' h' ≫ eqToHom (congrArg X.X (show r' = r by omega)) := by
  subst r
  subst r'
  exact (Category.comp_id (a.v p (p + q) rfl)).symm

/--
概要：写像複体の cone 比較は connecting map と右 shift 比較に関して可換。
方針：第一射影の合成公式と標準三角形の負号を各成分で照合する。
規約：shift の同型と cone の同型を独立に変更しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の三角構造の比較。
-/
theorem mappingConeComparison_connecting (T : CochainComplex C ℤ)
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    mappingConeComparison A T f ≫ mappingPostcompose A T (mappingCone.triangle f).mor₃ =
      (mappingCone.triangle (mappingPostcompose A T f)).mor₃ ≫ mappingShiftMap A T X 1 := by
  ext q z
  change (mappingCone.liftCochain f
    ((mappingCone.fst (mappingPostcompose A T f)).val.v q (q + 1) rfl z)
    ((mappingCone.snd (mappingPostcompose A T f)).v q q (add_zero q) z) rfl).comp
      (Cochain.ofHom (mappingCone.triangle f).mor₃) (add_zero q) =
    (((mappingCone.triangle (mappingPostcompose A T f)).mor₃.f q) z).rightShift 1 q rfl
  ext p r h
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, coneConnecting_component]
  simp only [Preadditive.comp_neg]
  simp only [Preadditive.neg_comp, ← Category.assoc]
  have hv := mappingCone.liftCochain_v_fst_v f
    ((mappingCone.fst (mappingPostcompose A T f)).val.v q (q + 1) rfl z)
    ((mappingCone.snd (mappingPostcompose A T f)).v q q (add_zero q) z)
    rfl p r (r + 1) h rfl
  apply (congrArg (fun k => -(k ≫ (X.shiftFunctorObjXIso 1 r (r + 1) rfl).inv)) hv).trans
  simp [coneConnecting_component, Cochain.rightShift, Cochain.mk_v,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, Category.assoc]
  subst r
  change -((ModuleCat.Hom.hom ((mappingCone.fst (mappingPostcompose A T f)).val.v
      q (q + 1) rfl)) z).v p (p + q + 1) (by omega) =
    (-((ModuleCat.Hom.hom ((mappingCone.fst (mappingPostcompose A T f)).val.v
      q (q + 1) rfl)) z)).v p (p + (q + 1)) rfl ≫
      eqToHom (congrArg X.X (show p + (q + 1) = p + q + 1 by omega))
  exact cochain_component_transport
    (-((ModuleCat.Hom.hom ((mappingCone.fst (mappingPostcompose A T f)).val.v
      q (q + 1) rfl)) z)) p (p + q + 1) (p + (q + 1)) (by omega) rfl

end SerrePositivity.KST.DerivedGeometry.LinearComplex
