module
public import SerrePositivity.InfinityCategories.Derived.DGUnitCompositionMap
/-!
概要：元の端点を保つ単位成分と左右合成を、実分解の同じ計算へ接続する。
方針：対象の一致と成分の異種等式を抽象的な全 Hom 合成へ渡す。
規約：全次数を保持し、出力射影性を仮定しない。使われ方：厳密 dg 自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex DGNerve
lemma dgUnitPostcompMap_heq {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
    {x y z x' y' z' : D}
    (i : 𝟙_ (Complex R) ⟶ homObject R D y z)
    (j : 𝟙_ (Complex R) ⟶ homObject R D y' z')
    (hx : x = x') (hy : y = y') (hz : z = z') (hij : HEq i j) :
    HEq (dgUnitPostcompMap (R := R) (D := D) (x := x) i)
      (dgUnitPostcompMap (R := R) (D := D) (x := x') j) := by
  subst x' y' z'
  cases eq_of_heq hij
  rfl
lemma dgUnitPrecompMap_heq {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
    {x y z x' y' z' : D}
    (i : 𝟙_ (Complex R) ⟶ homObject R D x y)
    (j : 𝟙_ (Complex R) ⟶ homObject R D x' y')
    (hx : x = x') (hy : y = y') (hz : z = z') (hij : HEq i j) :
    HEq (dgUnitPrecompMap (R := R) (D := D) (z := z) i)
      (dgUnitPrecompMap (R := R) (D := D) (z := z') j) := by
  subst x' y' z'
  cases eq_of_heq hij
  rfl
end SerrePositivity.InfinityCategories
