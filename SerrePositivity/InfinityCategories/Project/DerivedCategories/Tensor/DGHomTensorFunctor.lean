module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGHomTensorMap
/-!
概要：有限個の実対象の充満像を使い、Small 性なしの Hom dg 関手を構成する。
方針：同じ代表作用を、小さい対角双加群と有限実充満像の局所計算へ比較する。
規約：元の dg 圏に Small 性を追加しない。使われ方：二変数の導来 Hom の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory Opposite
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
/-- 二つの実対象の充満像を使い、実単位の保存を証明する。 -/
lemma dgHomTensorMap_identity (x : DGTensorCategory R Cᵒᵖ C) :
    eId (Complex R) x ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C x x =
      identity (homObject R C x.1.unop x.2) := by
  let f : Fin 2 → C := ![x.1.unop, x.2]
  let a : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨0⟩
  let b : _root_.SerrePositivity.InfinityCategories.DGObjectImage f := ⟨1⟩
  have h := (Bimodule.diagonal R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)).uncurryHom_identity (op a, b)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_diagonal] at h
  exact h
/-- 任意の有限実充満像に沿う、全 Hom 合成の保存。 -/
lemma dgHomTensorMap_composition_finiteImage (n : ℕ) (f : Fin n → C)
    (i j k a b c : Fin n) :
    eComp (Complex R) (C := DGTensorCategory R Cᵒᵖ C) (op (f i), f a)
      (op (f j), f b) (op (f k), f c) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op (f i), f a) (op (f k), f c) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op (f i), f a) (op (f j), f b) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C (op (f j), f b) (op (f k), f c)) ≫
        enrichedComposition _ _ _ := by
  let x : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) := (op ⟨i⟩, ⟨a⟩)
  let y : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) := (op ⟨j⟩, ⟨b⟩)
  let z : DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.DGObjectImage f) := (op ⟨k⟩, ⟨c⟩)
  have h := (Bimodule.diagonal R (_root_.SerrePositivity.InfinityCategories.DGObjectImage f)).uncurryHom_comp x y z
  simp only [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap_diagonal] at h
  exact h
/-- 六つの実対象の充満像から、元の任意の全 Hom 合成を検証する。 -/
lemma dgHomTensorMap_composition (x y z : DGTensorCategory R Cᵒᵖ C) :
    eComp (Complex R) x y z ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C x z =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C x y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C y z) ≫
        enrichedComposition _ _ _ := by
  have h := dgHomTensorMap_composition_finiteImage R C 6
    ![x.1.unop, y.1.unop, z.1.unop, x.2, y.2, z.2] 0 1 2 3 4 5
  dsimp only [Matrix.cons_val] at h
  exact h
/-- 任意の大きさの dg 圏の同じ局所 Hom を値とする実二入力 dg 関手。 -/
def dgHomTensorFunctor : DGFunctor R (DGTensorCategory R Cᵒᵖ C) (Complex R) where
  obj x := homObject R C x.1.unop x.2
  map := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTensorMap R C
  map_id x := dgHomTensorMap_identity R C x
  map_comp x y z := dgHomTensorMap_composition R C x y z
end SerrePositivity.InfinityCategories.Project.DerivedCategories
