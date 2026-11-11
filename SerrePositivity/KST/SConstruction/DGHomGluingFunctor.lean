module
public import SerrePositivity.KST.SConstruction.DGHomGluingClosedFamily

/-! # 元の全 Hom 自然な閉比較からの標準 Hom gluing 関手
概要：元の四関手と閉比較を、Hom 双加群に沿う実 dg gluing の関手へ送る。
方針：同じ閉比較の自然性を実 augmentation へ移し、全 Hom の関手法則を使う。
規約：対象・比較・左右関手を保持。使われ方：Milnor 四角形の対角と商。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (p.obj (L.obj x)) ⟶
    ForgetEnrichment.of (Complex R) (q.obj (G.obj x)))
  (h : ∀ x y, (L.comp p).map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (p.obj (L.obj x))) (a y) =
    (G.comp q).map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (q.obj (G.obj y))))

/-- 元の閉比較そのものから構成する、全 Hom を持つ実 Hom gluing 関手。 -/
def dgHomGluingFunctor :
    DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :=
  dgStrictGluingFunctor R C D (dgHomGluingBimodule R C D E p q) L G
    (dgHomGluingComparisonCycle R C D E p q L G a)
    (dgHomGluingComparison_naturality R C D E p q L G a h)

/-- 同じ実関手は、元の左右対象と閉比較を持つ対象を厳密に回収する。 -/
lemma dgHomGluingFunctor_obj (x : P) :
    (dgHomGluingFunctor R C D E p q L G a h).obj x =
      dgHomGluingComparisonObject R C D E p q L G a x := rfl

/-- 同じ実関手の左射影は、元の左関手そのもの。 -/
lemma dgHomGluingFunctor_left :
    (dgHomGluingFunctor R C D E p q L G a h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)) = L :=
  dgStrictGluingFunctor_left R C D (dgHomGluingBimodule R C D E p q) L G
    (dgHomGluingComparisonCycle R C D E p q L G a)
    (dgHomGluingComparison_naturality R C D E p q L G a h)

/-- 同じ実関手の右射影は、元の右関手そのもの。 -/
lemma dgHomGluingFunctor_right :
    (dgHomGluingFunctor R C D E p q L G a h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) = G :=
  dgStrictGluingFunctor_right R C D (dgHomGluingBimodule R C D E p q) L G
    (dgHomGluingComparisonCycle R C D E p q L G a)
    (dgHomGluingComparison_naturality R C D E p q L G a h)

/-- 同じ実対象の閉元は、元の標的内の閉比較そのもの。 -/
lemma dgHomGluingFunctor_comparison (x : P) :
    ((dgHomGluingFunctor R C D E p q L G a h).obj x).gluing =
      dgHomGluingComparisonCycle R C D E p q L G a x := rfl

end SerrePositivity.KST.SConstruction
