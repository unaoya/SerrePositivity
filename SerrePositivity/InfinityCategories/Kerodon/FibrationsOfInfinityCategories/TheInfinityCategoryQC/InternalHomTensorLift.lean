module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：二つの内部 Hom 成分を直積への射に合わせる。
方針：各成分を uncurry して直積へ合わせ、再び curry する。
規約：試験対象とパラメータは任意の単体集合。
使われ方：直積内の図式の錐族の構成。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：指定した二成分の内部 Hom の族を直積へ合わせる。
方針：uncurry 後に直積の lift を作る。
規約：二成分の間に適合条件は不要。
使われ方：直積の錐族の全パラメータの lift。 -/
def internalHomTensorLift {K T X Y : SSet.{u}}
    (a : T ⟶ (ihom K).obj X) (b : T ⟶ (ihom K).obj Y) : T ⟶ (ihom K).obj (X ⊗ Y) :=
  curry (CartesianMonoidalCategory.lift (uncurry a) (uncurry b))

/-- 概要：直積への内部 Hom の lift は第一成分を保つ。
方針：uncurry の単射性と直積の第一射影の式を使う。
規約：射の厳密な等式。
使われ方：直積の錐族の第一成分。 -/
lemma internalHomTensorLift_fst {K T X Y : SSet.{u}}
    (a : T ⟶ (ihom K).obj X) (b : T ⟶ (ihom K).obj Y) :
    internalHomTensorLift a b ≫ (ihom K).map (fst X Y) = a := by
  apply uncurry_injective
  rw [uncurry_natural_right, internalHomTensorLift, uncurry_curry, lift_fst]

/-- 概要：直積への内部 Hom の lift は第二成分を保つ。
方針：uncurry の単射性と直積の第二射影の式を使う。
規約：射の厳密な等式。
使われ方：直積の錐族の第二成分。 -/
lemma internalHomTensorLift_snd {K T X Y : SSet.{u}}
    (a : T ⟶ (ihom K).obj X) (b : T ⟶ (ihom K).obj Y) :
    internalHomTensorLift a b ≫ (ihom K).map (snd X Y) = b := by
  apply uncurry_injective
  rw [uncurry_natural_right, internalHomTensorLift, uncurry_curry, lift_snd]

/-- 概要：直積への内部 Hom の射は二成分で決まる。
方針：uncurry 後に直積の射の外延性を使う。
規約：quasicategory 性は要求しない。
使われ方：錐族の図式固定と射の一意性。 -/
lemma internalHomTensor_hom_ext {K T X Y : SSet.{u}}
    {a b : T ⟶ (ihom K).obj (X ⊗ Y)}
    (h₁ : a ≫ (ihom K).map (fst X Y) = b ≫ (ihom K).map (fst X Y))
    (h₂ : a ≫ (ihom K).map (snd X Y) = b ≫ (ihom K).map (snd X Y)) : a = b := by
  apply uncurry_injective
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [uncurry_natural_right] using congrArg uncurry h₁
  · simpa only [uncurry_natural_right] using congrArg uncurry h₂

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
