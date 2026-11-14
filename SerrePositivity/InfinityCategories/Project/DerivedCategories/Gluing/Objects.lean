module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
双加群に沿う dg gluing の対象と比較差。Kuznetsov–Lunts §4.1。
`Bimodule R C D` は C に反変、D に共変であり、`M.value c d` を φ(d,c) と読む。
比較差は (f,g) ↦ gμ − νf。全作用は既存の豊穣関手から取る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 二成分と、双加群の同じ値に属する閉次数零の元。 -/
structure DGGluingObject where
  left : C
  right : D
  gluing : zeroCycles (M.value left right)

variable {R C D M}
/-- 閉元を、単位複体からの実鎖写像として読む。 -/
def DGGluingObject.gluingMap (X : DGGluingObject R C D M) :
    𝟙_ (Complex R) ⟶ M.value X.left X.right :=
  unitFromCycle _ X.gluing

variable (R C D M) (X Y : DGGluingObject R C D M)
/-- 左成分の射に標的の閉元を前合成する全 Hom 鎖写像 νf。 -/
def dgGluingLeftAction : homObject R C X.left Y.left ⟶ M.value X.left Y.right :=
  (λ_ _).inv ≫
    (Y.gluingMap ⊗ₘ (M.rightAt Y.right).map (op Y.left) (op X.left)) ≫
      evaluation (M.value Y.left Y.right) (M.value X.left Y.right)

/-- 右成分の射を始域の閉元に作用させる全 Hom 鎖写像 gμ。 -/
def dgGluingRightAction : homObject R D X.right Y.right ⟶ M.value X.left Y.right :=
  (λ_ _).inv ≫
    (X.gluingMap ⊗ₘ (M.leftAt X.left).map X.right Y.right) ≫
      evaluation (M.value X.left X.right) (M.value X.left Y.right)

/-- gluing の Hom を定める実鎖写像 (f,g) ↦ gμ − νf。 -/
def dgGluingDifference :
    (homObject R C X.left Y.left ⊞ homObject R D X.right Y.right) ⟶
      M.value X.left Y.right :=
  biprod.snd ≫ dgGluingRightAction R C D M X Y -
    biprod.fst ≫ dgGluingLeftAction R C D M X Y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KL "Construction §4.1"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject
