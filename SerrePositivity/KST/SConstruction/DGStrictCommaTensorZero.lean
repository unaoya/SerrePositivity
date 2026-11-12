module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TensorPrimitiveTransport

/-! # 指定した比較零元の tensor 合成における保存
概要：元の全比較 cochain を消す二つの実鎖写像は、tensor 合成後も同じ比較を零にする。
方針：全パラメータの tensor 比較を、零 cochain と恒等係数写像で特殊化する。
規約：次数零だけで判定しない。使われ方：厳密な二成分 comma 関手の合成保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable {R : Type u} [CommRing R]

/-- 第一の比較 cochain の零性は、二つの全 Hom 作用の tensor で保存される。 -/
lemma dgStrictCommaTensorRight_zero {P H Q J T U : Complex R} (n : ℤ)
    (a : P ⟶ H) (b : Q ⟶ J) (h : Cochain H T n) (m : T ⊗ J ⟶ U)
    (hh : (Cochain.ofHom a).comp h (zero_add n) = 0) :
    (Cochain.ofHom (a ⊗ₘ b)).comp
      (((tensorRightHom J H T).f n h).comp (Cochain.ofHom m) (add_zero n))
      (zero_add n) = 0 := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTensorRightPrimitive_transport n a b (𝟙 T) (𝟙 U)
    (0 : Cochain P T n) h ((𝟙 T ⊗ₘ b) ≫ m) m
    (by simpa only [Cochain.zero_comp] using hh) (Category.comp_id _).symm
  simpa only [map_zero, Cochain.zero_comp] using ht

/-- 第二の比較 cochain の零性も、二つの全 Hom 作用の tensor で保存される。 -/
lemma dgStrictCommaTensorLeft_zero {P H Q J T U : Complex R} (n : ℤ)
    (a : P ⟶ H) (b : Q ⟶ J) (h : Cochain J T n) (m : H ⊗ T ⟶ U)
    (hh : (Cochain.ofHom b).comp h (zero_add n) = 0) :
    (Cochain.ofHom (a ⊗ₘ b)).comp
      (((tensorLeftHom H J T).f n h).comp (Cochain.ofHom m) (add_zero n))
      (zero_add n) = 0 := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTensorLeftPrimitive_transport n a b (𝟙 T) (𝟙 U)
    (0 : Cochain Q T n) h ((a ⊗ₘ 𝟙 T) ≫ m) m
    (by simpa only [Cochain.zero_comp] using hh) (Category.comp_id _).symm
  simpa only [map_zero, Cochain.zero_comp] using ht

end SerrePositivity.KST.SConstruction
