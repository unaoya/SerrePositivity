module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection

/-!
概要：dg 双加群への実 derivation と、それが定める平方零代数への切断を構成する。
方針：derivation は chain map と単位・Leibniz 則を持ち、直和の graph を代数射にする。
規約：微分との整合は chain map に含む。使われ方：導来平方零拡大の具体的模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Preadditive
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)

@[ext]
structure Derivation where
  hom : A.X ⟶ M.X
  unit : η[A.X] ≫ hom = 0
  leibniz : μ[A.X] ≫ hom = (A.X ◁ hom) ≫ M.actLeft + (hom ▷ A.X) ≫ M.actRight

def Derivation.section (d : Derivation A M) : A ⟶ algebra A M := by
  refine Mon.Hom.mk' (biprod.lift (𝟙 A.X) d.hom) ?_ ?_
  · change η[A.X] ≫ biprod.lift (𝟙 A.X) d.hom = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.one A M
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.one, biprod.inl_fst, Category.comp_id]
    · simp only [Category.assoc, biprod.lift_snd, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.one, biprod.inl_snd, comp_zero, d.unit]
  · change μ[A.X] ≫ biprod.lift (𝟙 A.X) d.hom =
      (biprod.lift (𝟙 A.X) d.hom ⊗ₘ biprod.lift (𝟙 A.X) d.hom) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul A M
    apply biprod.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_fst, biprod.lift_fst,
        tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
        tensorHom_id, id_whiskerRight]
    · simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_snd, comp_add, tensorHom_comp_tensorHom_assoc,
        biprod.lift_fst, biprod.lift_snd, id_tensorHom, tensorHom_id] using d.leibniz

lemma Derivation.section_projection (d : Derivation A M) :
    d.section ≫ projection A M = 𝟙 A := by
  apply Mon.Hom.ext
  exact biprod.lift_fst _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
