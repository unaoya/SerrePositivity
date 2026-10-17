module
public import SerrePositivity.DifferentialGraded.Resolution.BoundaryCells
public import Mathlib.Logic.Small.List

/-! # 任意次数・異なる端点を持つdg生成cellのpath項

既存Homを間に置き、新生成元を任意整数次数のsphereで表す。
ここでの微分は内部微分のみ。指定境界による追加微分は後続で構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)

/-- 生成元はsource→targetの次数degreeの射で、微分は指定cycle。 -/
structure Family where
  source : I → D
  target : I → D
  degree : I → ℤ
  boundary : ∀ i, complexCycles A (homObject A D (source i) (target i)) (degree i + 1)

namespace Family
variable (C : Family A D I)

abbrev generator (i : I) : Complex A := complexSphere A (C.degree i)

/-- 空語には既存Homを置く。生成元の両端を同じ対象と仮定しない。 -/
def term : List I → D → D → Complex A
  | [], x, y => homObject A D x y
  | i :: w, x, y => homObject A D x (C.source i) ⊗
      (C.generator A D I i ⊗ term w (C.target i) y)

/-- 指定生成元を、その両端の単位とともに一生成元pathへ入れる。 -/
def generatorTerm (i : I) : C.generator A D I i ⟶ C.term A D I [i] (C.source i) (C.target i) :=
  (λ_ (C.generator A D I i)).inv ≫
    (eId (Complex A) (C.source i) ⊗ₘ
      ((ρ_ (C.generator A D I i)).inv ≫
        (𝟙 (C.generator A D I i) ⊗ₘ eId (Complex A) (C.target i))))

lemma term_kFlat (hD : localHomKFlat A D) (w : List I) (x y : D) :
    complexKFlat A (C.term A D I w x y) := by
  induction w generalizing x y with
  | nil => exact hD x y
  | cons i w ih =>
    exact complexKFlat_tensor A (hD x (C.source i))
      (complexKFlat_tensor A (complexSphere_kFlat A (C.degree i)) (ih (C.target i) y))

variable [Small.{u} I]

abbrev internalHom (x y : D) : Complex A := ∐ (fun w : List I => C.term A D I w x y)

def inclusion (w : List I) (x y : D) : C.term A D I w x y ⟶ C.internalHom A D I x y :=
  Sigma.ι (fun w : List I => C.term A D I w x y) w

def originalHom (x y : D) : homObject A D x y ⟶ C.internalHom A D I x y :=
  C.inclusion A D I [] x y

def generatorInclusion (i : I) :
    C.generator A D I i ⟶ C.internalHom A D I (C.source i) (C.target i) :=
  C.generatorTerm A D I i ≫ C.inclusion A D I [i] (C.source i) (C.target i)

lemma internalHom_ext (x y : D) {T : Complex A}
    (f g : C.internalHom A D I x y ⟶ T)
    (h : ∀ w, C.inclusion A D I w x y ≫ f = C.inclusion A D I w x y ≫ g) : f = g :=
  Sigma.hom_ext f g h

lemma internalHom_kFlat (hD : localHomKFlat A D) (x y : D) :
    complexKFlat A (C.internalHom A D I x y) := by
  have : HasExactColimitsOfShape (Discrete (List I)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (List I)).symm)
  exact complexKFlat_colimit A (Discrete.functor fun w : List I => C.term A D I w x y)
    (fun w => C.term_kFlat A D I hD w.as x y)

end Family

/-- 増大関手のホモロジー核を消すために使う全境界cellの族。 -/
def boundaryFamily (E : Type z) [DGCategory A E] (F : DGFunctor A D E) :
    Family A D (DGCategoryBoundaryCells.Index A D E F) where
  source i := i.1
  target i := i.2.1
  degree i := i.2.2.degree
  boundary i := i.2.2.cycle

end SerrePositivity.DifferentialGraded.DGCellAttachment
