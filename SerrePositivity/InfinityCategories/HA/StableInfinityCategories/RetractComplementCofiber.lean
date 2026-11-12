module
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
/-!
概要：retract の補射影を第一射とする三角形の cofiber を d ⊕ Σd と同定する。
方針：Hom の完全性で二つの分裂写像を取り、交差成分を除いて双積の逆射を作る。
規約：補対象や冪等射の分裂を追加で選ばず、指定した retract の射を使う。
使われ方：D-22 の完全な冪等完備化射の本質像の判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- retract の補射影の任意の distinguished cofiber は、元の対象とその懸垂の双積。 -/
lemma retractComplementCofiber_biprodShift {X d z : C}
    (i : d ⟶ X) (r : X ⟶ d) (hir : i ≫ r = 𝟙 d)
    (g : X ⟶ z) (h : z ⟶ X⟦(1 : ℤ)⟧)
    (ht : Triangle.mk (𝟙 X - r ≫ i) g h ∈ distTriang C) :
    Nonempty (biprod d (d⟦(1 : ℤ)⟧) ≅ z) := by
  let T := Triangle.mk (𝟙 X - r ≫ i) g h
  have hgh : g ≫ h = 0 := comp_distTriang_mor_zero₂₃ T ht
  have hhq : h ≫ (𝟙 X - r ≫ i)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ T ht
  obtain ⟨a, ha⟩ := T.yoneda_exact₂ ht r (by
    change (𝟙 X - r ≫ i) ≫ r = 0
    simp only [sub_comp, Category.id_comp, Category.assoc, hir, Category.comp_id, sub_self])
  have hiq : i ≫ (𝟙 X - r ≫ i) = 0 := by
    simp only [comp_sub, Category.comp_id, ← Category.assoc, hir, Category.id_comp, sub_self]
  obtain ⟨j, hj⟩ := T.coyoneda_exact₁ ht (i⟦(1 : ℤ)⟧') (by
    change i⟦(1 : ℤ)⟧' ≫ (𝟙 X - r ≫ i)⟦(1 : ℤ)⟧' = 0
    rw [← CategoryTheory.Functor.map_comp, hiq, CategoryTheory.Functor.map_zero])
  change z ⟶ d at a
  change r = g ≫ a at ha
  change d⟦(1 : ℤ)⟧ ⟶ z at j
  change i⟦(1 : ℤ)⟧' = j ≫ h at hj
  let k : d ⟶ z := i ≫ g
  let p : z ⟶ d⟦(1 : ℤ)⟧ := h ≫ r⟦(1 : ℤ)⟧'
  let j' : d⟦(1 : ℤ)⟧ ⟶ z := j - (j ≫ a) ≫ k
  have hka : k ≫ a = 𝟙 d := by
    dsimp [k]
    rw [Category.assoc, ← ha, hir]
  have hkh : k ≫ h = 0 := by simp only [k, Category.assoc, hgh, comp_zero]
  have hkp : k ≫ p = 0 := by simp only [p, ← Category.assoc, hkh, zero_comp]
  have hja : j' ≫ a = 0 := by
    simp only [j', sub_comp, Category.assoc, hka, Category.comp_id, sub_self]
  have hjh : j' ≫ h = i⟦(1 : ℤ)⟧' := by
    simp only [j', sub_comp, Category.assoc, hkh, comp_zero, sub_zero, ← hj]
  have hjp : j' ≫ p = 𝟙 (d⟦(1 : ℤ)⟧) := by
    rw [show p = h ≫ r⟦(1 : ℤ)⟧' from rfl, ← Category.assoc, hjh,
      ← CategoryTheory.Functor.map_comp, hir, CategoryTheory.Functor.map_id]
  have hpih : p ≫ i⟦(1 : ℤ)⟧' = h := by
    have hh := hhq
    rw [CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_id,
      comp_sub, Category.comp_id] at hh
    have hh' : h = h ≫ (r ≫ i)⟦(1 : ℤ)⟧' := sub_eq_zero.mp hh
    simpa only [p, CategoryTheory.Functor.map_comp, Category.assoc] using hh'.symm
  let E : z ⟶ z := 𝟙 z - a ≫ k - p ≫ j'
  have hEh : E ≫ h = 0 := by
    simp only [E, sub_comp, Category.id_comp, Category.assoc, hkh, comp_zero, sub_zero]
    rw [hjh, hpih, sub_self]
  obtain ⟨v, hv⟩ := T.coyoneda_exact₃ ht E hEh
  change z ⟶ X at v
  change E = v ≫ g at hv
  have hEa : E ≫ a = 0 := by
    simp only [E, sub_comp, Category.id_comp, Category.assoc, hka, Category.comp_id,
      hja, comp_zero, sub_self]
  have hvr : v ≫ r = 0 := by rw [ha, ← Category.assoc, ← hv, hEa]
  have hvq : v ≫ (𝟙 X - r ≫ i) = v := by
    simp only [comp_sub, Category.comp_id, ← Category.assoc, hvr, zero_comp, sub_zero]
  have hqg : (𝟙 X - r ≫ i) ≫ g = 0 := comp_distTriang_mor_zero₁₂ T ht
  have hE : E = 0 := by
    rw [hv, ← hvq, Category.assoc, hqg, comp_zero]
  have htotal : a ≫ k + p ≫ j' = 𝟙 z := by
    change 𝟙 z - a ≫ k - p ≫ j' = 0 at hE
    apply eq_comm.mp
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hE)
  refine ⟨
    { hom := biprod.desc k j'
      inv := biprod.lift a p
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩
  · ext <;> simp [Category.assoc, hka, hkp, hja, hjp]
  · simpa only [biprod.lift_desc] using htotal

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
