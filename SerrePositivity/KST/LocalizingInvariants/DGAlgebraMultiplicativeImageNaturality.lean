module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeSimplexImage

/-!
概要：全単体と連結成分の局所化比較は、元の源・標的射の両方に自然。
方針：実増大の全標的自然性と、元の反転後の合成式を用いる。
規約：対象別の比較に弱めず、元の前合成・後合成をそのまま保つ。
使われ方：導来写像空間比較の二変数の零次正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (L : Mon (Complex R) ⥤ C) (hL : InvertsQuasiIsos R L) {A A' B B' : Mon (Complex R)}

private lemma simplexImagePost {U V W Z Z' : C} (a : U ⟶ V) (i : Z ⟶ V)
    (j : Z' ⟶ W) (t : V ⟶ W) (q : Z ⟶ Z') [IsIso i] [IsIso j]
    (h : i ≫ t = q ≫ j) : (a ≫ t) ≫ inv j = (a ≫ inv i) ≫ q := by
  apply (cancel_mono j).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

lemma multiplicativeSimplexImage_precompose (n : SimplexCategoryᵒᵖ)
    (f : A' ⟶ A) (a : A ⟶ (multiplicativeSimplices R B).obj n) :
    multiplicativeSimplexImage R L hL n (f ≫ a) =
      L.map f ≫ multiplicativeSimplexImage R L hL n a := by
  letI := hL ((multiplicativeSimplicesAugmentation R B).app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B n)
  change L.map (f ≫ a) ≫ inv (L.map ((multiplicativeSimplicesAugmentation R B).app n)) =
    L.map f ≫ (L.map a ≫ inv (L.map ((multiplicativeSimplicesAugmentation R B).app n)))
  rw [L.map_comp, Category.assoc]

lemma multiplicativeSimplexImage_postcompose (n : SimplexCategoryᵒᵖ)
    (a : A ⟶ (multiplicativeSimplices R B).obj n) (q : B ⟶ B') :
    multiplicativeSimplexImage R L hL n (a ≫ (multiplicativeSimplicesMap R q).app n) =
      multiplicativeSimplexImage R L hL n a ≫ L.map q := by
  letI := hL ((multiplicativeSimplicesAugmentation R B).app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B n)
  letI := hL ((multiplicativeSimplicesAugmentation R B').app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B' n)
  have h := congr_app ((multiplicativeSimplicesConstant R).naturality q) n
  change q ≫ (multiplicativeSimplicesAugmentation R B').app n =
    (multiplicativeSimplicesAugmentation R B).app n ≫ (multiplicativeSimplicesMap R q).app n at h
  have hm : L.map ((multiplicativeSimplicesAugmentation R B).app n) ≫
      L.map ((multiplicativeSimplicesMap R q).app n) =
        L.map q ≫ L.map ((multiplicativeSimplicesAugmentation R B').app n) := by
    rw [← L.map_comp, ← L.map_comp]
    exact congrArg L.map h.symm
  change L.map (a ≫ (multiplicativeSimplicesMap R q).app n) ≫
      inv (L.map ((multiplicativeSimplicesAugmentation R B').app n)) =
    (L.map a ≫ inv (L.map ((multiplicativeSimplicesAugmentation R B).app n))) ≫ L.map q
  rw [L.map_comp]
  exact simplexImagePost (L.map a)
    (L.map ((multiplicativeSimplicesAugmentation R B).app n))
    (L.map ((multiplicativeSimplicesAugmentation R B').app n))
    (L.map ((multiplicativeSimplicesMap R q).app n)) (L.map q) hm

lemma multiplicativeMappingPiZeroImage_precompose (f : A' ⟶ A)
    (x : SSet.π₀ (multiplicativeMappingSimplices R A B)) :
    multiplicativeMappingPiZeroImage R L hL
      (SSet.mapπ₀ (multiplicativeMappingPrecompose R f B) x) =
        L.map f ≫ multiplicativeMappingPiZeroImage R L hL x := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective x
  change multiplicativeSimplexImage R L hL (op ⦋0⦌) (f ≫ a) = _
  exact multiplicativeSimplexImage_precompose R L hL (op ⦋0⦌) f a

lemma multiplicativeMappingPiZeroImage_postcompose (q : B ⟶ B')
    (x : SSet.π₀ (multiplicativeMappingSimplices R A B)) :
    multiplicativeMappingPiZeroImage R L hL
      (SSet.mapπ₀ (multiplicativeMappingPostcompose R A q) x) =
        multiplicativeMappingPiZeroImage R L hL x ≫ L.map q := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective x
  change multiplicativeSimplexImage R L hL (op ⦋0⦌)
    (a ≫ (multiplicativeSimplicesMap R q).app (op ⦋0⦌)) = _
  exact multiplicativeSimplexImage_postcompose R L hL (op ⦋0⦌) a q

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
