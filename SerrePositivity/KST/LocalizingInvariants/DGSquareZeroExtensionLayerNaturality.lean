module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionMap

/-!
概要：実平方零 class の模型射は、元の層同型を通じて元の係数射になる。
方針：実包含のホモロジー同型を消去し、零切断の cocone 比較の自然性へ帰着する。
規約：源の二次数の消滅は両端で明示。使われ方：像因子分解の二射の層での同定。
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
  (t : N.X ⟶ N'.X) (hb : b.hom = biprod.map q.hom t) (h : w ≫ a' = a ≫ b)

lemma kernelHomologyIso_naturality (j : ℤ) : homologyMap (kernelMap N N' q t) j ≫
    (kernelHomologyIso N' j).hom = (kernelHomologyIso N j).hom ≫ homologyMap t (j - 1) :=
  cochainNegInlCoconeHomologyIso_naturality q.hom t j

lemma layerHomologyIso_naturality (j : ℤ)
    (h₀ : IsZero (W.X.homology (j - 1))) (h₁ : IsZero (W.X.homology j))
    (h₀' : IsZero (W'.X.homology (j - 1))) (h₁' : IsZero (W'.X.homology j)) :
    homologyMap (map N N' a a' w q b t hb h).hom j ≫ (layerHomologyIso N' a' j h₀' h₁').hom =
      (layerHomologyIso N a j h₀ h₁).hom ≫ homologyMap t (j - 1) := by
  have := layerInclusion_homology_isIso N a j h₀ h₁
  apply (cancel_epi (homologyMap (layerInclusion N a) j)).1
  rw [← Category.assoc, ← homologyMap_comp, map_layerInclusion, homologyMap_comp,
    Category.assoc, layerInclusion_layerHomologyIso, ← Category.assoc,
    layerInclusion_layerHomologyIso]
  exact kernelHomologyIso_naturality N N' q t j

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
