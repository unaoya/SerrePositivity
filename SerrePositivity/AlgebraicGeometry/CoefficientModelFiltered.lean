module

public import SerrePositivity.AlgebraicGeometry.CoefficientModelImages
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
概要：元の環写像への有限型係数模型の全体は filtered。
方針：二対象の像を有限生成部分代数の和に入れ、平行射は像の模型で一致させる。
規約：元の環の Noether 性・v 判定はここでは要求しない。
使われ方：B03・B04 の被覆模型の final な部分圏と実際の余極限。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 二つの全模型は、有限生成部分代数による実際の共通の後段を持つ。 -/
theorem coefficientModelCategory_cocone_objs (X Y : CoefficientModelCategory k g) :
    ∃ (Z : CoefficientModelCategory k g) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  let A := X.hom.left.hom.range ⊔ Y.hom.left.hom.range
  let D := (A.map g ⊔ X.hom.right.hom.range) ⊔ Y.hom.right.hom.range
  have hA : A.FG := (fg_algHom_range (A := X.left.left.obj) X.hom.left.hom).sup (fg_algHom_range (A := Y.left.left.obj) Y.hom.left.hom)
  have hD : D.FG := ((hA.map g).sup (fg_algHom_range (A := X.left.right.obj) X.hom.right.hom)).sup
    (fg_algHom_range (A := Y.left.right.obj) Y.hom.right.hom)
  have hAD : A.map g ≤ D := le_trans le_sup_left le_sup_left
  have hAX : X.hom.left.hom.range ≤ A := le_sup_left
  have hAY : Y.hom.left.hom.range ≤ A := le_sup_right
  have hDX : X.hom.right.hom.range ≤ D := le_trans le_sup_right le_sup_left
  have hDY : Y.hom.right.hom.range ≤ D := le_sup_right
  let Z := coefficientModelSubalgebraObj g A D hA hD hAD
  let f : X ⟶ Z := coefficientModelToSubalgebraObj g A D hA hD hAD X
    (fun x ↦ hAX (AlgHom.mem_range_self _ x))
    (fun x ↦ hDX (AlgHom.mem_range_self _ x))
  let h : Y ⟶ Z := coefficientModelToSubalgebraObj g A D hA hD hAD Y
    (fun x ↦ hAY (AlgHom.mem_range_self _ x))
    (fun x ↦ hDY (AlgHom.mem_range_self _ x))
  exact ⟨Z, f, h, trivial⟩

/-- 全模型の平行射は、標的の実際の像の模型で一致する。 -/
theorem coefficientModelCategory_cocone_maps {X Y : CoefficientModelCategory k g}
    (f h : X ⟶ Y) : ∃ (Z : CoefficientModelCategory k g) (m : Y ⟶ Z), f ≫ m = h ≫ m := by
  refine ⟨coefficientModelImageObj g Y, coefficientModelToImage g Y, ?_⟩
  exact coefficientModelHom_eq_of_injective_target g
    (coefficientModelImage_base_injective g Y) (coefficientModelImage_source_injective g Y) _ _

instance : IsFiltered (CoefficientModelCategory k g) where
  cocone_objs := coefficientModelCategory_cocone_objs g
  cocone_maps _ _ f h := coefficientModelCategory_cocone_maps g f h

/-- 全模型の同じ宇宙の小さい添字。 -/
abbrev CoefficientModelIndex := SmallModel.{u} (CoefficientModelCategory k g)

instance : IsFiltered (CoefficientModelIndex g) :=
  IsFiltered.of_equivalence (equivSmallModel (CoefficientModelCategory k g))

end SerrePositivity.AlgebraicGeometry
