module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap

/-!
概要：係数射の合成と零化を、元の平方零代数射の合成へ移す。
方針：実直和射の二射影を計算し、底の恒等射と係数合成を保持する。
規約：係数の零化は underlying の実等式。使われ方：Postnikov class の cokernel 零経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A : Mon (Complex R)} {M N P : Bimod A A}
  (f : M ⟶ N) (g : N ⟶ P)

lemma coefficientMap_comp : coefficientMap A f ≫ coefficientMap A g =
    coefficientMap A (f ≫ g) := by
  apply Mon.Hom.ext
  change biprod.map (𝟙 A.X) f.hom ≫ biprod.map (𝟙 A.X) g.hom =
    biprod.map (𝟙 A.X) (f.hom ≫ g.hom)
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma coefficientMap_comp_zero (h : f.hom ≫ g.hom = 0) :
    coefficientMap A f ≫ coefficientMap A g = projection A M ≫ zeroSection A P := by
  apply Mon.Hom.ext
  change biprod.map (𝟙 A.X) f.hom ≫ biprod.map (𝟙 A.X) g.hom = biprod.fst ≫ biprod.inl
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp only [Category.assoc, biprod.map_snd, biprod.inl_snd, comp_zero]
    rw [← Category.assoc, biprod.map_snd, Category.assoc, h, comp_zero]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
