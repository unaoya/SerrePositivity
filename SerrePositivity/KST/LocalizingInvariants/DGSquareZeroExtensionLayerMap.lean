module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerNaturality
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodMapComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackSourceMap

/-!
概要：元の homotopy-pullback 模型射を、平方零係数の層ホモロジー自然性へ渡す。
方針：同じ三成分の実模型射を既存の層包含の自然性で計算する。
規約：元の class 可換式と零切断の可換式を保持。使われ方：実候補 roof の π₂ 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A A' W W' : Mon (Complex R)}
  (N : Bimod A A) (N' : Bimod A' A')
  (a : W ⟶ SquareZero.algebra A N) (a' : W' ⟶ SquareZero.algebra A' N')
  (w : W ⟶ W') (q : A ⟶ A') (b : SquareZero.algebra A N ⟶ SquareZero.algebra A' N')
  (t : N.X ⟶ N'.X) (hb : b.hom = biprod.map q.hom t)
  (hf : w ≫ a' = a ≫ b)
  (hg : q ≫ SquareZero.zeroSection A' N' = SquareZero.zeroSection A N ≫ b)

include hb in
lemma layerHomologyIso_map_naturality (j : ℤ)
    (h₀ : IsZero (W.X.homology (j - 1))) (h₁ : IsZero (W.X.homology j))
    (h₀' : IsZero (W'.X.homology (j - 1))) (h₁' : IsZero (W'.X.homology j)) :
    homologyMap (DGAlgebra.HomotopyPullbackModel.map R a (SquareZero.zeroSection A N)
      a' (SquareZero.zeroSection A' N') w b q hf hg).hom j ≫
        (layerHomologyIso N' a' j h₀' h₁').hom =
      (layerHomologyIso N a j h₀ h₁).hom ≫ homologyMap t (j - 1) :=
  layerHomologyIso_naturality N N' a a' w q b t hb hf j h₀ h₁ h₀' h₁'

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A A' B C : Mon (Complex R)}
  (f : A ⟶ B) (g : C ⟶ B) (a : A' ⟶ A)

lemma sourceMap_eq_map : sourceMap R f g a =
    map R (a ≫ f) g f g a (𝟙 B) (𝟙 C)
      (Category.comp_id _).symm (by simp) := by
  apply hom_ext R f g
  · rw [sourceMap_left, map_left]
  · rw [sourceMap_right, map_right, Category.comp_id]
  · rw [sourceMap_path, map_path, Path.map_id, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
