module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNormalizedRingShuffleCoherence
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroPaths
public import Mathlib.Algebra.Category.Ring.Basic
/-!
概要：単体環の実 shuffle 積と結合・両単位・準同型自然性。
方針：元の三重 shuffle の添字替えと三入力の像・符号を照合する。
規約：非可換な積の順序を保持する。使われ方：β5(g) の実正規化乗法。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite EInfinity.BarrattEccles
open scoped _root_.Simplicial
universe u
def simplicialRingShuffleProduct (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) : A.obj (op ⦋p + q⦌) :=
  ∑ s : ShufflePath p q, (s.sign : ℤ) •
    ((A.map s.horizontalMap.op).hom x * (A.map s.verticalMap.op).hom y)
lemma simplicialRingShuffleProduct_triple_first (A : SimplicialObject RingCat.{u})
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (x : A.obj (op ⦋p⦌)) :
    (A.map v.1.horizontalMap.op).hom ((A.map v.2.horizontalMap.op).hom x) =
      (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map (tripleShuffleEquiv p q r v).1.horizontalMap.op).hom x) := by
  have h := congrArg (fun f ↦ (A.map f.op).hom x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.triple_first p q r v)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.left_eq_horizontal, op_comp, Functor.map_comp,
    RingCat.hom_comp, RingHom.comp_apply] using h
lemma simplicialRingShuffleProduct_triple_second (A : SimplicialObject RingCat.{u})
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (y : A.obj (op ⦋q⦌)) :
    (A.map v.1.horizontalMap.op).hom ((A.map v.2.verticalMap.op).hom y) =
      (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map (tripleShuffleEquiv p q r v).1.verticalMap.op).hom
          ((A.map (tripleShuffleEquiv p q r v).2.horizontalMap.op).hom y)) := by
  have h := congrArg (fun f ↦ (A.map f.op).hom y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.triple_second p q r v)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.left_eq_horizontal,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.right_eq_vertical, op_comp, Functor.map_comp,
    RingCat.hom_comp, RingHom.comp_apply] using h
lemma simplicialRingShuffleProduct_triple_third (A : SimplicialObject RingCat.{u})
    (p q r : ℕ) (v : ShufflePath (p + q) r × ShufflePath p q)
    (z : A.obj (op ⦋r⦌)) :
    (A.map v.1.verticalMap.op).hom z =
      (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map (tripleShuffleEquiv p q r v).1.verticalMap.op).hom
          ((A.map (tripleShuffleEquiv p q r v).2.verticalMap.op).hom z)) := by
  have h := congrArg (fun f ↦ (A.map f.op).hom z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.triple_third p q r v)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.right_eq_vertical, op_comp, Functor.map_comp,
    RingCat.hom_comp, RingHom.comp_apply] using h
lemma simplicialRingShuffleProduct_assoc (A : SimplicialObject RingCat.{u}) (p q r : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) (z : A.obj (op ⦋r⦌)) :
    simplicialRingShuffleProduct A (p + q) r (simplicialRingShuffleProduct A p q x y) z =
      (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        (simplicialRingShuffleProduct A p (q + r) x
          (simplicialRingShuffleProduct A q r y z)) := by
  simp only [simplicialRingShuffleProduct, map_sum, map_zsmul, map_mul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp_rw [Finset.smul_sum, smul_smul]
  let L := fun v : ShufflePath (p + q) r × ShufflePath p q ↦
    ((v.1.sign : ℤ) * (v.2.sign : ℤ)) •
      ((A.map v.1.horizontalMap.op).hom ((A.map v.2.horizontalMap.op).hom x) *
        (A.map v.1.horizontalMap.op).hom ((A.map v.2.verticalMap.op).hom y) *
          (A.map v.1.verticalMap.op).hom z)
  let R := fun w : ShufflePath p (q + r) × ShufflePath q r ↦
    ((w.1.sign : ℤ) * (w.2.sign : ℤ)) •
      ((A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map w.1.horizontalMap.op).hom x) *
      ((A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map w.1.verticalMap.op).hom ((A.map w.2.horizontalMap.op).hom y)) *
      (A.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.associationMap p q r).op).hom
        ((A.map w.1.verticalMap.op).hom ((A.map w.2.verticalMap.op).hom z))))
  change (∑ a, ∑ b, L (a, b)) = ∑ a, ∑ b, R (a, b)
  rw [← Fintype.sum_prod_type L, ← Fintype.sum_prod_type R]
  apply Fintype.sum_equiv (tripleShuffleEquiv p q r)
  intro v
  dsimp only [L, R]
  rw [← Units.val_mul, ← Units.val_mul, tripleShuffle_sign]
  rw [simplicialRingShuffleProduct_triple_first,
    simplicialRingShuffleProduct_triple_second, simplicialRingShuffleProduct_triple_third,
    mul_assoc]
lemma simplicialRingShuffleProduct_naturality {A B : SimplicialObject RingCat.{u}}
    (f : A ⟶ B) (p q : ℕ) (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    (f.app (op ⦋p + q⦌)).hom (simplicialRingShuffleProduct A p q x y) =
      simplicialRingShuffleProduct B p q ((f.app (op ⦋p⦌)).hom x)
        ((f.app (op ⦋q⦌)).hom y) := by
  have hn {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m) (z : A.obj n) :
      (f.app m).hom ((A.map a).hom z) = (B.map a).hom ((f.app n).hom z) := by
    have h := congrArg (fun g ↦ g.hom z) (f.naturality a)
    simpa only [RingCat.hom_comp, RingHom.comp_apply] using h
  simp only [simplicialRingShuffleProduct, map_sum, map_zsmul, map_mul, hn]
lemma simplicialRingShuffleProduct_right_unit (A : SimplicialObject RingCat.{u})
    (p : ℕ) (x : A.obj (op ⦋p⦌)) :
    simplicialRingShuffleProduct A p 0 x 1 = x := by
  let : Unique (ShufflePath p 0) :=
    { default := zeroRightPath p
      uniq := fun s ↦ s.rightZero_unique _ }
  have hh : (default : ShufflePath p 0).horizontalMap = 𝟙 ⦋p⦌ := by
    ext k
    exact congrArg Fin.val ((default : ShufflePath p 0).horizontal_rightZero k)
  simp only [simplicialRingShuffleProduct, Fintype.sum_unique, ShufflePath.sign_rightZero,
    Units.val_one, one_smul, map_one, mul_one, hh]
  change (A.map (𝟙 (op ⦋p⦌))).hom x = x
  rw [A.map_id]
  rfl
def zeroLeftShuffleDegreeMap (q : ℕ) : ⦋0 + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := Fin.cast (congrArg Nat.succ (Nat.zero_add q))
      monotone' := fun _ _ h ↦ h }
lemma simplicialRingShuffleProduct_left_unit (A : SimplicialObject RingCat.{u})
    (q : ℕ) (y : A.obj (op ⦋q⦌)) :
    simplicialRingShuffleProduct A 0 q 1 y = (A.map (zeroLeftShuffleDegreeMap q).op).hom y := by
  let : Unique (ShufflePath 0 q) :=
    { default := zeroLeftPath q
      uniq := fun s ↦ s.leftZero_unique _ }
  have hv : (default : ShufflePath 0 q).verticalMap = zeroLeftShuffleDegreeMap q := by
    ext k
    exact (default : ShufflePath 0 q).vertical_leftZero_val k
  simp only [simplicialRingShuffleProduct, Fintype.sum_unique, ShufflePath.sign_leftZero,
    Units.val_one, one_smul, map_one, one_mul, hv]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
