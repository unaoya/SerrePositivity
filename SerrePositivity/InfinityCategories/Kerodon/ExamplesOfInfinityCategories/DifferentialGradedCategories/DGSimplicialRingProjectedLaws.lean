module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DGSimplicialRingShuffleProjection
/-!
概要：実 shuffle 積の退化零化と正規化射影の整合性。
方針：共通退化因子・PInfty の補射影と元の実結合・単位を接続する。
規約：非可換な積の順序と元の全次数を保つ。使われ方：β5(g) の正規化 dg 代数化。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open EInfinity.BarrattEccles
open scoped _root_.Simplicial
def ringShuffleDegreeMap {m n : ℕ} (h : m = n) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.cast (congrArg Nat.succ h)
      monotone' := fun _ _ hmn ↦ hmn }
lemma ringNormalizedProjection_degreeMap (A : SimplicialObject RingCat.{u})
    {m n : ℕ} (h : m = n) (x : A.obj (op ⦋n⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f m).hom
        ((A.map (ringShuffleDegreeMap h).op).hom x) =
      (A.map (ringShuffleDegreeMap h).op).hom
        (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f n).hom x) := by
  cases h
  have hm : ringShuffleDegreeMap (rfl : m = m) = 𝟙 ⦋m⦌ := rfl
  rw [hm]
  change ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f m).hom
    ((A.map (𝟙 (op ⦋m⦌))).hom x) =
      (A.map (𝟙 (op ⦋m⦌))).hom
        (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f m).hom x)
  rw [A.map_id]
  rfl
lemma projectedRingShuffleProduct_assoc (A : SimplicialObject RingCat.{u}) (p q r : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) (z : A.obj (op ⦋r⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q + r)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A (p + q) r
        (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + q)).hom
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y)) z) =
    (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
      (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (p + (q + r))).hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p (q + r) x
          (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (q + r)).hom
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A q r y z)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_left_projection A (p + q) r
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y) z]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.projectedRingShuffleProduct_right_projection A p (q + r) x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A q r y z)]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_assoc]
  exact ringNormalizedProjection_degreeMap A (Nat.add_assoc p q r) _
lemma projectedRingShuffleProduct_right_unit (A : SimplicialObject RingCat.{u})
    (p : ℕ) (x : A.obj (op ⦋p⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f p).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p 0 x 1) =
        ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f p).hom x := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_right_unit]
lemma projectedRingShuffleProduct_left_unit (A : SimplicialObject RingCat.{u})
    (q : ℕ) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f (0 + q)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A 0 q 1 y) =
    (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.zeroLeftShuffleDegreeMap q).op).hom
      (((PInfty (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)).f q).hom y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct_left_unit]
  exact ringNormalizedProjection_degreeMap A (Nat.zero_add q) y
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
