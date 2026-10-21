module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift

/-!
概要：実 dg 双加群の shift 上に、符号付き tensor–shift 同型を使う左右作用を定義する。
方針：左作用には右因子の符号付き shift、右作用には左因子の shift を使う。
規約：作用三則は後続で検証。使われ方：Postnikov 拡大の shift した係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} (M : Bimod A A) (s : ℤ)

def actLeft : A.X ⊗ M.X⟦s⟧ ⟶ M.X⟦s⟧ :=
  (cochainTensorShiftRight A.X M.X s).hom ≫ M.actLeft⟦s⟧'

def actRight : M.X⟦s⟧ ⊗ A.X ⟶ M.X⟦s⟧ :=
  (cochainTensorShiftLeft M.X A.X s).hom ≫ M.actRight⟦s⟧'

lemma actLeft_naturality {N : Bimod A A} (f : M ⟶ N) :
    actLeft M s ≫ f.hom⟦s⟧' = (A.X ◁ f.hom⟦s⟧') ≫ actLeft N s := by
  unfold actLeft
  rw [Category.assoc, ← Functor.map_comp, f.left_act_hom, Functor.map_comp]
  have hn := cochainTensorShiftRight_naturality (P := A.X) f.hom s
  change (A.X ◁ f.hom⟦s⟧') ≫ (cochainTensorShiftRight A.X N.X s).hom =
    (cochainTensorShiftRight A.X M.X s).hom ≫ (A.X ◁ f.hom)⟦s⟧' at hn
  rw [← Category.assoc, ← hn, Category.assoc]

lemma actRight_naturality {N : Bimod A A} (f : M ⟶ N) :
    actRight M s ≫ f.hom⟦s⟧' = (f.hom⟦s⟧' ▷ A.X) ≫ actRight N s := by
  unfold actRight
  rw [Category.assoc, ← Functor.map_comp, f.right_act_hom, Functor.map_comp]
  have hn := cochainTensorShiftLeft_naturality (Q := A.X) f.hom s
  change (f.hom⟦s⟧' ▷ A.X) ≫ (cochainTensorShiftLeft N.X A.X s).hom =
    (cochainTensorShiftLeft M.X A.X s).hom ≫ (f.hom ▷ A.X)⟦s⟧' at hn
  rw [← Category.assoc, ← hn, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGBimoduleShift
