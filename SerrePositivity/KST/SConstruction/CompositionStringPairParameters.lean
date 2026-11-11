module
public import SerrePositivity.KST.SConstruction.CompositionStringParameters

/-! # 三精密化から保存済みの二入力補正パラメータへの射影
概要：合成射の精密化を保持した共通パラメータから、元の二入力の積へ写す。
方針：元の二つの nerve 射影を同じ tensor 積への射対にする。
規約：射影後の二族は元の入力射の全精密化そのもの。
使われ方：保存済み BF 補正列と元の合成比較三角形の共通パラメータ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {I : Type u} [SmallCategory I] {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 三つの全精密化から、元の二入力の全精密化の積への実射影。 -/
def compositionStringPair : nerve (CompositionStringParameters f g) ⟶
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⊗ nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g) :=
  lift (nerveMap (compositionStringFirst f g)) (nerveMap (compositionStringSecond f g))

/-- 第一射影は、元の前の射の全精密化への射影。 -/
lemma compositionStringPair_first :
    compositionStringPair f g ≫ fst _ _ = nerveMap (compositionStringFirst f g) := lift_fst _ _

/-- 第二射影は、元の後の射の全精密化への射影。 -/
lemma compositionStringPair_second :
    compositionStringPair f g ≫ snd _ _ = nerveMap (compositionStringSecond f g) := lift_snd _ _

end SerrePositivity.KST.SConstruction
