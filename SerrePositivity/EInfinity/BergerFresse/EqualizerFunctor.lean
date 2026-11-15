module

public import SerrePositivity.EInfinity.BergerFresse.ProductDiagram
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# 元のBF convolution等化子の全関手

Berger–Fresse §2.2・§3.1、M14 L22、報告 §401。
元の全積の二つの射を各対象で等化し、同じ射を包含で判定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BergerFresse
open CategoryTheory Limits
open SerrePositivity.Cosimplicial (CosimplicialAlgebra)
variable (A : Type u) [CommRing A]

/-- 元の全次数のconvolutionの前後合成の等化子（BF §3.1）。 -/
def bfNormalizedObj (X : CosimplicialAlgebra A) : (BarrattEccles.operad A).Algebra :=
  equalizer ((post A).app X) ((pre A).app X)

/-- 同じ元の積の射を元の等化子へ持ち上げる（BF §3.1）。 -/
def bfNormalizedMap {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    bfNormalizedObj A X ⟶ bfNormalizedObj A Y :=
  equalizer.lift (equalizer.ι ((post A).app X) ((pre A).app X) ≫
    (convolutionProductFunctor A).map f) (by
      rw [Category.assoc, post_naturality, ← Category.assoc, equalizer.condition,
        Category.assoc, ← pre_naturality]
      exact (Category.assoc _ _ _).symm)

/-- L22：同じ元の積と等化子で作るBF代数の全関手（BF §3.1）。 -/
def bfNormalizedAlgebra : CosimplicialAlgebra A ⥤ (BarrattEccles.operad A).Algebra where
  obj := bfNormalizedObj A
  map := bfNormalizedMap A
  map_id X := by
    apply equalizer.hom_ext
    simp only [bfNormalizedMap, equalizer.lift_ι, Category.id_comp]
    let i := equalizer.ι ((post A).app X) ((pre A).app X)
    exact (congrArg (fun h => i ≫ h) ((convolutionProductFunctor A).map_id X)).trans
      (Category.comp_id i)
  map_comp f g := by
    apply equalizer.hom_ext
    simp only [bfNormalizedMap, Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      Functor.map_comp]

/-- L22：元の等化子の射は恒等を保つ（BF §3.1）。 -/
lemma bfNormalizedAlgebra_map_id (X : CosimplicialAlgebra A) :
    bfNormalizedMap A (𝟙 X) = 𝟙 (bfNormalizedObj A X) :=
  (bfNormalizedAlgebra A).map_id X

/-- L22：元の等化子の射は合成を保つ（BF §3.1）。 -/
lemma bfNormalizedAlgebra_map_comp {X Y Z : CosimplicialAlgebra A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    bfNormalizedMap A (f ≫ g) = bfNormalizedMap A f ≫ bfNormalizedMap A g :=
  (bfNormalizedAlgebra A).map_comp f g

end SerrePositivity.EInfinity.BergerFresse
