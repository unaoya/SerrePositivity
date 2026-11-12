module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementMap

/-!
概要：置換前の mapping path の単位は厳密自然であり、置換後の単位の二合成は同じ射影を持つ。
方針：引き戻しの両射影と定数 path の自然性を計算する。
規約：置換後の単位の厳密自然性は主張しない。使われ方：全 Hom での相対自然性の充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet

open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.MappingPathComparison

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma map_unit (n : ℕ) : (KanSequence.mappingPathComparison (sequenceHom p)).app n ≫
    (map p q a b h).app n =
      a.app n ≫ (KanSequence.mappingPathComparison (sequenceHom q)).app n := by
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_unit (p.app n) (q.app n) (a.app n) (b.app n)
    (congrArg (fun f ↦ f.app n) h)

end MappingPathComparison
namespace FibrationReplacementComparison

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

lemma unit_comparison (n : ℕ) :
    ((fibrationReplacementUnit p) ≫ map p q a b h).app n ≫
        (fibrationReplacementComparison q).app n =
      (a ≫ fibrationReplacementUnit q).app n ≫ (fibrationReplacementComparison q).app n := by
  change ((fibrationReplacementUnit p).app n ≫ (map p q a b h).app n) ≫ _ =
    (a.app n ≫ (fibrationReplacementUnit q).app n) ≫ _
  rw [Category.assoc, map_comparison, ← Category.assoc, fibrationReplacementUnit_comparison,
    MappingPathComparison.map_unit, Category.assoc, fibrationReplacementUnit_comparison]

end FibrationReplacementComparison
end SerrePositivity.KST.LocalizingInvariants
