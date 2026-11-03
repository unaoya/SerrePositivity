module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # graph 生成元射の合成を抽象複体で貼り合わせる
概要：tensor 生成元の比較に終端の射を追加し、元の合成射を保つ。
方針：抽象複体の圏法則だけで二つの回収式を合成する。
規約：具体的 coend を展開しない。使われ方：graph の三重比較の生成元計算。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 左 tensor 生成元の元の比較と、終端での同じ回収式を合成する。 -/
lemma dgTensorLeft_generator_comp {H J K T Z U V : Complex A}
    (i : J ⟶ K) (o : H ⊗ K ⟶ Z) (p : Z ⟶ U) (a : K ⟶ T)
    (j : H ⊗ T ⟶ U) (v : J ⟶ T) (r : U ⟶ V) (w : H ⊗ T ⟶ V)
    (ho : o ≫ p = (𝟙 H ⊗ₘ a) ≫ j) (ha : i ≫ a = v) (hj : j ≫ r = w) :
    ((H ◁ i) ≫ o) ≫ p ≫ r = (H ◁ v) ≫ w := by
  have ht := tensorLeft_generator_map i o p a j v ho ha
  have hc := congrArg (fun k => k ≫ r) ht
  simpa only [Category.assoc, hj] using hc

end SerrePositivity.KST.SConstruction
