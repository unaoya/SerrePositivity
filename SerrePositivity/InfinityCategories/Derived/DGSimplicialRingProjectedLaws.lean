module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingShuffleProjection
/-!
概要：実 shuffle 積の退化零化と正規化射影の整合性。
方針：共通退化因子・PInfty の補射影と元の実結合・単位を接続する。
規約：非可換な積の順序と元の全次数を保つ。使われ方：β5(g) の正規化 dg 代数化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open EInfinity.BarrattEccles
open scoped Simplicial
def ringShuffleDegreeMap {m n : ℕ} (h : m = n) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.cast (congrArg Nat.succ h)
      monotone' := fun _ _ hmn ↦ hmn }
lemma ringNormalizedProjection_degreeMap (A : SimplicialObject RingCat.{u})
    {m n : ℕ} (h : m = n) (x : A.obj (op ⦋n⦌)) :
    ((PInfty (X := simplicialRingIntegerModule A)).f m).hom
        ((A.map (ringShuffleDegreeMap h).op).hom x) =
      (A.map (ringShuffleDegreeMap h).op).hom
        (((PInfty (X := simplicialRingIntegerModule A)).f n).hom x) := by
  cases h
  have hm : ringShuffleDegreeMap (rfl : m = m) = 𝟙 ⦋m⦌ := rfl
  rw [hm]
  change ((PInfty (X := simplicialRingIntegerModule A)).f m).hom
    ((A.map (𝟙 (op ⦋m⦌))).hom x) =
      (A.map (𝟙 (op ⦋m⦌))).hom
        (((PInfty (X := simplicialRingIntegerModule A)).f m).hom x)
  rw [A.map_id]
  rfl
lemma projectedRingShuffleProduct_assoc (A : SimplicialObject RingCat.{u}) (p q r : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) (z : A.obj (op ⦋r⦌)) :
    ((PInfty (X := simplicialRingIntegerModule A)).f (p + q + r)).hom
      (simplicialRingShuffleProduct A (p + q) r
        (((PInfty (X := simplicialRingIntegerModule A)).f (p + q)).hom
          (simplicialRingShuffleProduct A p q x y)) z) =
    (A.map (NormalizedRingShuffle.associationMap p q r).op).hom
      (((PInfty (X := simplicialRingIntegerModule A)).f (p + (q + r))).hom
        (simplicialRingShuffleProduct A p (q + r) x
          (((PInfty (X := simplicialRingIntegerModule A)).f (q + r)).hom
            (simplicialRingShuffleProduct A q r y z)))) := by
  rw [projectedRingShuffleProduct_left_projection A (p + q) r
    (simplicialRingShuffleProduct A p q x y) z]
  rw [projectedRingShuffleProduct_right_projection A p (q + r) x
    (simplicialRingShuffleProduct A q r y z)]
  rw [simplicialRingShuffleProduct_assoc]
  exact ringNormalizedProjection_degreeMap A (Nat.add_assoc p q r) _
lemma projectedRingShuffleProduct_right_unit (A : SimplicialObject RingCat.{u})
    (p : ℕ) (x : A.obj (op ⦋p⦌)) :
    ((PInfty (X := simplicialRingIntegerModule A)).f p).hom
      (simplicialRingShuffleProduct A p 0 x 1) =
        ((PInfty (X := simplicialRingIntegerModule A)).f p).hom x := by
  rw [simplicialRingShuffleProduct_right_unit]
lemma projectedRingShuffleProduct_left_unit (A : SimplicialObject RingCat.{u})
    (q : ℕ) (y : A.obj (op ⦋q⦌)) :
    ((PInfty (X := simplicialRingIntegerModule A)).f (0 + q)).hom
      (simplicialRingShuffleProduct A 0 q 1 y) =
    (A.map (zeroLeftShuffleDegreeMap q).op).hom
      (((PInfty (X := simplicialRingIntegerModule A)).f q).hom y) := by
  rw [simplicialRingShuffleProduct_left_unit]
  exact ringNormalizedProjection_degreeMap A (Nat.zero_add q) y
end SerrePositivity.InfinityCategories
