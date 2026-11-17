module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates
public import Mathlib.CategoryTheory.Functor.Basic

/-!
概要：同じ反変・共変の両端を持つ射の列を、twisted arrowの一つの長い単体にする。
方針：左半分に始域の逆順、右半分に標的の順序を置き、元の零番の射でつなぐ。
規約：IS-W2 R03dの指定された射の全次数表示。新たな逆や単体充填は選ばない。
使われ方：全source frameの要素を正本のtwisted arrowへ送る写像の各単体。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)

/-- 同じ長い単体の左半分の、元の逆順の添字。 -/
def twistedPairingLeftIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : i.val < n+1) : Fin (n+1) :=
  ⟨n-i.val, by omega⟩

/-- 同じ長い単体の右半分の、元の順序の添字。 -/
def twistedPairingRightIndex {n : ℕ} (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) : Fin (n+1) :=
  ⟨i.val-(n+1), by have := i.isLt; omega⟩

variable {n : ℕ} (σ : Fin (n+1) ⥤ I)

/-- 左半分から右半分への射は、元の零番の射を同じ両端の作用で送る。 -/
def twistedPairingCross (a b : Fin (n+1)) :
    (A.obj (σ.obj a)).unop ⟶ B.obj (σ.obj b) :=
  (A.map (σ.map (homOfLE (show (0 : Fin (n+1)) ≤ a by exact Fin.zero_le a)))).unop ≫
    h (σ.obj 0) ≫ B.map (σ.map (homOfLE (show (0 : Fin (n+1)) ≤ b by exact Fin.zero_le b)))

/-- 同じ交差射の左側の合成則。 -/
theorem twistedPairingCross_left (a b c : Fin (n+1)) (hab : b ≤ a) :
    (A.map (σ.map (homOfLE hab))).unop ≫ twistedPairingCross A B h σ b c =
      twistedPairingCross A B h σ a c := by
  dsimp only [twistedPairingCross]
  rw [← Category.assoc, ← CategoryTheory.unop_comp, ← A.map_comp, ← σ.map_comp]
  congr 3

/-- 同じ交差射の右側の合成則。 -/
theorem twistedPairingCross_right (a b c : Fin (n+1)) (hbc : b ≤ c) :
    twistedPairingCross A B h σ a b ≫ B.map (σ.map (homOfLE hbc)) =
      twistedPairingCross A B h σ a c := by
  dsimp only [twistedPairingCross]
  simp only [Category.assoc, ← B.map_comp, ← σ.map_comp]
  congr 3

/-- 両半分の対象を持つ、同じ長い単体の対象列。 -/
def twistedPairingSimplexObj (i : Fin (n+n+1+1)) : C :=
  if hi : i.val < n+1 then (A.obj (σ.obj (twistedPairingLeftIndex i hi))).unop
  else B.obj (σ.obj (twistedPairingRightIndex i hi))

/-- 左半分の対象の指定された型の移送。 -/
theorem twistedPairingSimplexObj_left (i : Fin (n+n+1+1)) (hi : i.val < n+1) :
    twistedPairingSimplexObj A B σ i = (A.obj (σ.obj (twistedPairingLeftIndex i hi))).unop := by
  simp only [twistedPairingSimplexObj, dite_eq_left hi]

/-- 右半分の対象の指定された型の移送。 -/
theorem twistedPairingSimplexObj_right (i : Fin (n+n+1+1)) (hi : ¬ i.val < n+1) :
    twistedPairingSimplexObj A B σ i = B.obj (σ.obj (twistedPairingRightIndex i hi)) := by
  simp only [twistedPairingSimplexObj, dite_eq_right hi]

/-- 同じ対象の移送を両側で行うと、元の射の合成は保持される。 -/
theorem twistedPairingTransport_comp {X Y Z U V W : C} (p : X = U) (q : Y = V) (r : Z = W)
    {f : U ⟶ V} {g : V ⟶ W} {k : U ⟶ W} (hk : k = f ≫ g) :
    eqToHom p ≫ k ≫ eqToHom r.symm =
      (eqToHom p ≫ f ≫ eqToHom q.symm) ≫ (eqToHom q ≫ g ≫ eqToHom r.symm) := by
  subst U V W
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hk

/-- 同じ対象の移送は、元の射そのものを異種等式で保持する。 -/
theorem twistedPairingTransport_heq {X Y U V : C} (p : X = U) (q : Y = V) (f : U ⟶ V) :
    HEq (eqToHom p ≫ f ≫ eqToHom q.symm) f := by
  subst U V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, heq_eq_eq]

/-- 元の両端の射と交差射を使う、長い単体のすべての射。 -/
def twistedPairingSimplexMap (i j : Fin (n+n+1+1)) (hij : i ≤ j) :
    twistedPairingSimplexObj A B σ i ⟶ twistedPairingSimplexObj A B σ j := by
  by_cases hi : i.val < n+1
  · by_cases hj : j.val < n+1
    · exact eqToHom (twistedPairingSimplexObj_left A B σ i hi) ≫
        (A.map (σ.map (homOfLE (show twistedPairingLeftIndex j hj ≤
          twistedPairingLeftIndex i hi by dsimp [twistedPairingLeftIndex]; exact Nat.sub_le_sub_left hij _)))).unop ≫
        eqToHom (twistedPairingSimplexObj_left A B σ j hj).symm
    · exact eqToHom (twistedPairingSimplexObj_left A B σ i hi) ≫
        twistedPairingCross A B h σ (twistedPairingLeftIndex i hi) (twistedPairingRightIndex j hj) ≫
        eqToHom (twistedPairingSimplexObj_right A B σ j hj).symm
  · have hj : ¬ j.val < n+1 := fun h => hi (lt_of_le_of_lt hij h)
    exact eqToHom (twistedPairingSimplexObj_right A B σ i hi) ≫
      B.map (σ.map (homOfLE (show twistedPairingRightIndex i hi ≤
        twistedPairingRightIndex j hj by dsimp [twistedPairingRightIndex]; exact Nat.sub_le_sub_right hij _))) ≫
      eqToHom (twistedPairingSimplexObj_right A B σ j hj).symm

/-- 同じ長い単体の射は恒等射を保つ。 -/
theorem twistedPairingSimplexMap_id (i : Fin (n+n+1+1)) :
    twistedPairingSimplexMap A B h σ i i le_rfl = 𝟙 _ := by
  by_cases hi : i.val < n+1
  · simp [twistedPairingSimplexMap, hi]
  · simp [twistedPairingSimplexMap, hi]

/-- 同じ長い単体の射は、左・交差・右の元の合成を保つ。 -/
theorem twistedPairingSimplexMap_comp (i j k : Fin (n+n+1+1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    twistedPairingSimplexMap A B h σ i k (hij.trans hjk) =
      twistedPairingSimplexMap A B h σ i j hij ≫ twistedPairingSimplexMap A B h σ j k hjk := by
  by_cases hi : i.val < n+1
  · by_cases hj : j.val < n+1
    · by_cases hk : k.val < n+1
      · simp only [twistedPairingSimplexMap, dite_eq_left hi, dite_eq_left hj, dite_eq_left hk]
        apply twistedPairingTransport_comp
          (twistedPairingSimplexObj_left A B σ i hi)
          (twistedPairingSimplexObj_left A B σ j hj)
          (twistedPairingSimplexObj_left A B σ k hk)
        rw [← CategoryTheory.unop_comp, ← A.map_comp, ← σ.map_comp]
        congr 3
      · simp only [twistedPairingSimplexMap, dite_eq_left hi, dite_eq_left hj, dite_eq_right hk]
        apply twistedPairingTransport_comp
          (twistedPairingSimplexObj_left A B σ i hi)
          (twistedPairingSimplexObj_left A B σ j hj)
          (twistedPairingSimplexObj_right A B σ k hk)
        exact (twistedPairingCross_left A B h σ _ _ _ _).symm
    · have hk : ¬ k.val < n+1 := fun h => hj (lt_of_le_of_lt hjk h)
      simp only [twistedPairingSimplexMap, dite_eq_left hi, dite_eq_right hj, dite_eq_right hk]
      apply twistedPairingTransport_comp
        (twistedPairingSimplexObj_left A B σ i hi)
        (twistedPairingSimplexObj_right A B σ j hj)
        (twistedPairingSimplexObj_right A B σ k hk)
      exact (twistedPairingCross_right A B h σ _ _ _ _).symm
  · have hj : ¬ j.val < n+1 := fun h => hi (lt_of_le_of_lt hij h)
    have hk : ¬ k.val < n+1 := fun h => hj (lt_of_le_of_lt hjk h)
    simp only [twistedPairingSimplexMap, dite_eq_right hi, dite_eq_right hj, dite_eq_right hk]
    apply twistedPairingTransport_comp
      (twistedPairingSimplexObj_right A B σ i hi)
      (twistedPairingSimplexObj_right A B σ j hj)
      (twistedPairingSimplexObj_right A B σ k hk)
    rw [← B.map_comp, ← σ.map_comp]
    congr 2

/-- 元の一つの射の列を、同じ両端を持つ長い通常nerveの単体へ送る。 -/
def twistedPairingSimplex : Fin (n+n+1+1) ⥤ C where
  obj := twistedPairingSimplexObj A B σ
  map f := twistedPairingSimplexMap A B h σ _ _ (leOfHom f)
  map_id i := twistedPairingSimplexMap_id A B h σ i
  map_comp f g := twistedPairingSimplexMap_comp A B h σ _ _ _ (leOfHom f) (leOfHom g)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
