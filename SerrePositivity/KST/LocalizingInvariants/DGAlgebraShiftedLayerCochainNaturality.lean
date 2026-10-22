module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayerHomology

/-!
概要：shift 層の自然なホモロジー同型を、元の層 cochain 射に対して述べる。
方針：双加群射の underlying 射の式を既存自然性に代入する。
規約：任意の非負 Postnikov 段と整数 shift。使われ方：実係数逆の両三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n) (s : ℤ)

lemma postnikovShiftedLayerHomologyIso_cochain_naturality :
    homologyMap ((postnikovLayerMap R f n)⟦s⟧') (-(n + 1) - s) ≫
      (postnikovShiftedLayerHomologyIso R C n hn s).hom =
        (postnikovShiftedLayerHomologyIso R B n hn s).hom ≫ homologyMap f.hom (-(n + 1)) := by
  simpa only [postnikovShiftedLayerMap_hom] using
    postnikovShiftedLayerHomologyIso_naturality R B n hn s f

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
