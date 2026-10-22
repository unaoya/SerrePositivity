module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCochainHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderPrism

/-! 主 cochain ホモトピーの全円柱写像を、同じ実 extension の後合成として回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CochainComplex HomComplex DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingComplexPinchedHomotopy_of_cochain_h :
    (dgGluingComplexPinchedHomotopy_of_cochain.{u, v} f g h he).h =
      (dgGluingComplexPinchedCylinderHomotopy.{u, v} K).h ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderExtension f g h he) := by
  dsimp only [dgGluingComplexPinchedHomotopy_of_cochain]
  rw [dgGluingHomotopyRetarget_h]
  rfl

lemma dgGluingComplexPinchedHomotopy_of_cochain_prism :
    (β_ (Δ[1] : SSet.{max u v}) (complexPinchedSpace.{u, v} K)).hom ≫
        (dgGluingComplexPinchedHomotopy_of_cochain.{u, v} f g h he).h =
      dgGluingComplexPinchedCylinderPrism.{u, v} K ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderExtension f g h he) := by
  rw [dgGluingComplexPinchedHomotopy_of_cochain_h, ← Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
