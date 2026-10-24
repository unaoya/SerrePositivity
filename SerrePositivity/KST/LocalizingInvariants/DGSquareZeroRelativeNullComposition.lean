module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeReverseCongr

/-!
概要：二つの class 経路に沿う零経路の輸送を、元の全経路のまま合成する。
方針：逆経路と affine 合成の線形式を比較する。
規約：同じ底・始点・終点を保つ。使われ方：fⱼ 自然性に続く W の模型終点。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {A T : Mon (Complex R)} {N : Bimod A A}
  {q : T ⟶ A} {a b c z : T ⟶ algebra A N}

lemma reverse_comp_null_hom (v : RelativeWitness q N a b) (w : RelativeWitness q N b c)
    (p : RelativeWitness q N a z) :
    ((v.comp w).reverse.comp p).hom = (w.reverse.comp (v.reverse.comp p)).hom := by
  apply Mon.Hom.ext
  rw [comp_hom_linear, reverse_hom_linear, comp_hom_linear,
    comp_hom_linear, reverse_hom_linear, comp_hom_linear, reverse_hom_linear]
  abel

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
