module
public import SerrePositivity.DifferentialGraded.Quotient.ScalarExtensionPaths
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionDiagrams
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition

/-! # 係数変更と有限 path の先頭合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded.ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

lemma termBaseChangeIso_cons_compare {S : Set D} (b : S) (w : Word S) (x y : D) :
    (termBaseChangeIso φ D (b :: w) x y).hom =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x b.val)))
        (compareTensor φ (sphereIso φ (-1)).hom (termBaseChangeIso φ D w b.val y).hom) := by
  rw [termBaseChangeIso_cons_hom]
  simp only [compareTensor, id_tensorHom]

lemma composition_baseChange (x y z : D) :
    (extension φ).map (eComp (Complex A) x y z) ≫ 𝟙 _ =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x y)))
        (𝟙 ((extension φ).obj (homObject A D y z))) ≫
          eComp (Complex A') (C := DGBaseChange φ D) x y z := by
  change _ ≫ 𝟙 _ = ((tensorIso φ _ _).hom ≫ (𝟙 _ ⊗ₘ 𝟙 _)) ≫
    ((tensorIso φ _ _).inv ≫ (extension φ).map (eComp (Complex A) x y z))
  simp only [tensorHom_id, id_whiskerRight, Category.comp_id, Iso.hom_inv_id_assoc]

lemma prependMap_baseChange {S : Set D} (w : Word S) (x y z : D) :
    (extension φ).map (prependMap A D w x y z) ≫ (termBaseChangeIso φ D w x z).hom =
      compareTensor φ (𝟙 ((extension φ).obj (homObject A D x y)))
        (termBaseChangeIso φ D w y z).hom ≫ prependMap A' (DGBaseChange φ D) w x y z := by
  cases w with
  | nil => exact composition_baseChange φ D x y z
  | cons b w =>
    let U := homObject A D x y
    let V := homObject A D y b.val
    let W := homObject A D x b.val
    let T := epsilonComplex A ⊗ term A D w b.val z
    let T' := epsilonComplex A' ⊗ term A' (DGBaseChange φ D) w b.val z
    let t : (extension φ).obj T ⟶ T' :=
      compareTensor φ (sphereIso φ (-1)).hom (termBaseChangeIso φ D w b.val z).hom
    let c : U ⊗ V ⟶ W := eComp (Complex A) x y b.val
    let c' := eComp (Complex A') (C := DGBaseChange φ D) x y b.val
    have ht := compareTensor_naturality φ c (𝟙 T) c' (𝟙 T')
      (a := compareTensor φ (𝟙 ((extension φ).obj U)) (𝟙 ((extension φ).obj V)))
      (b := t) (c := 𝟙 ((extension φ).obj W)) (d := t)
      (composition_baseChange φ D x y b.val) (by simp)
    have ha := compareTensor_associator_inv φ
      (𝟙 ((extension φ).obj U)) (𝟙 ((extension φ).obj V)) t
    simp only [prependMap, CategoryTheory.Functor.map_comp, Category.assoc,
      termBaseChangeIso_cons_compare]
    change (extension φ).map (α_ U V T).inv ≫
      (extension φ).map (c ⊗ₘ 𝟙 T) ≫ compareTensor φ (𝟙 _) t =
        compareTensor φ (𝟙 _) (compareTensor φ (𝟙 _) t) ≫
          (α_ _ _ T').inv ≫ (c' ⊗ₘ 𝟙 T')
    rw [ht, ← Category.assoc, ha, Category.assoc]

set_option maxHeartbeats 800000 in
-- 再帰する path の tensor 比較の型を各段階で照合する。
lemma appendMap_baseChange {S : Set D} (w v : Word S) (x y z : D) :
    (extension φ).map (appendMap A D w v x y z) ≫
        (termBaseChangeIso φ D (w ++ v) x z).hom =
      compareTensor φ (termBaseChangeIso φ D w x y).hom (termBaseChangeIso φ D v y z).hom ≫
        appendMap A' (DGBaseChange φ D) w v x y z := by
  induction w generalizing x y z with
  | nil => exact prependMap_baseChange φ D v x y z
  | cons b w ih =>
    let H := homObject A D x b.val
    let E := epsilonComplex A
    let P := term A D w b.val y
    let Q := term A D v y z
    let R := term A D (w ++ v) b.val z
    let H' := homObject A' (DGBaseChange φ D) x b.val
    let E' := epsilonComplex A'
    let P' := term A' (DGBaseChange φ D) w b.val y
    let Q' := term A' (DGBaseChange φ D) v y z
    let R' := term A' (DGBaseChange φ D) (w ++ v) b.val z
    let e : (extension φ).obj E ⟶ E' := (sphereIso φ (-1)).hom
    let p : (extension φ).obj P ⟶ P' := (termBaseChangeIso φ D w b.val y).hom
    let q : (extension φ).obj Q ⟶ Q' := (termBaseChangeIso φ D v y z).hom
    let r : (extension φ).obj R ⟶ R' := (termBaseChangeIso φ D (w ++ v) b.val z).hom
    let f : P ⊗ Q ⟶ R := appendMap A D w v b.val y z
    let f' : P' ⊗ Q' ⟶ R' := appendMap A' (DGBaseChange φ D) w v b.val y z
    have ht := compareTensor_naturality φ (𝟙 E) f (𝟙 E') f'
      (a := e) (b := compareTensor φ p q) (c := e) (d := r) (by simp) (ih b.val y z)
    have ha := compareTensor_associator φ e p q
    let g : (E ⊗ P) ⊗ Q ⟶ E ⊗ R := (α_ E P Q).hom ≫ E ◁ f
    let g' : (E' ⊗ P') ⊗ Q' ⟶ E' ⊗ R' := (α_ E' P' Q').hom ≫ E' ◁ f'
    have hg : (extension φ).map g ≫ compareTensor φ e r =
        compareTensor φ (compareTensor φ e p) q ≫ g' := by
      dsimp only [g, g']
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
      erw [ht]
      rw [← Category.assoc, ha, Category.assoc]
      rw [id_tensorHom]
    have houter := compareTensor_naturality φ (𝟙 H) g (𝟙 H') g'
      (a := 𝟙 H') (b := compareTensor φ (compareTensor φ e p) q)
      (c := 𝟙 H') (d := compareTensor φ e r)
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl) hg
    have hα := compareTensor_associator φ (𝟙 H') (compareTensor φ e p) q
    simp only [appendMap, List.cons_append, CategoryTheory.Functor.map_comp, Category.assoc,
      termBaseChangeIso_cons_compare]
    change (extension φ).map (α_ H (E ⊗ P) Q).hom ≫
      (extension φ).map (H ◁ g) ≫ compareTensor φ (𝟙 H') (compareTensor φ e r) =
        compareTensor φ (compareTensor φ (𝟙 H') (compareTensor φ e p)) q ≫
          (α_ H' (E' ⊗ P') Q').hom ≫ H' ◁ g'
    erw [houter]
    rw [← Category.assoc, hα, Category.assoc]
    rw [id_tensorHom]

end SerrePositivity.DifferentialGraded.DGQuotient
