module
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements

/-! # 左加群の全次数パラメータ付き自然性の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma leftParamNaturality_apply_of_sum {K : Complex A} {N N' : LeftModule A D}
    (a : ∀ x : D, K ⟶ homComplex A (N.obj x) (N'.obj x))
    (ha : ∀ x y : D, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ a y) ≫ enrichedComposition _ _ _ =
        (a x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _)
    {x y : D} {k p r s l n : ℤ} (t : K.X k) (f : GradedHom A x y p)
    (m : (N.obj x).X r) (hs : r + p = s) (hl : r + k = l) (hn : s + k = n) :
    ((a y).f k t).v s n hn (leftAction A N f m hs) =
      (k * p).negOnePow • leftAction A N' f (((a x).f k t).v r l hl m) (by omega) := by
  let ar : ∀ x : Dᵒᵖᵒᵖ, K ⟶ homComplex A (N.obj x.unop.unop) (N'.obj x.unop.unop) :=
    fun x => a x.unop.unop
  have har : ∀ x y : Dᵒᵖᵒᵖ, (β_ K (x ⟶[Complex A] y)).hom ≫
      (N.toRightOpposite.map x y ⊗ₘ ar y) ≫ enrichedComposition _ _ _ =
        (ar x ⊗ₘ N'.toRightOpposite.map x y) ≫ enrichedComposition _ _ _ := by
    intro x y
    change (β_ K (x.unop.unop ⟶[Complex A] y.unop.unop)).hom ≫
        ((𝟙 _ ≫ N.map x.unop.unop y.unop.unop) ⊗ₘ a y.unop.unop) ≫
          enrichedComposition _ _ _ =
      (a x.unop.unop ⊗ₘ (𝟙 _ ≫ N'.map x.unop.unop y.unop.unop)) ≫
        enrichedComposition _ _ _
    simpa only [Category.id_comp, leftAction] using ha x.unop.unop y.unop.unop
  have h := moduleParamNaturality_apply_of_sum A
    (M := N.toRightOpposite) (N := N'.toRightOpposite) ar har (m := k + p) (n := n) t
    (x := op (op x)) (y := op (op y)) f m rfl (by omega) hs hl
  change ((a y).f k t).v s n hn
      (((𝟙 _ ≫ N.map x y).f p f).v r s hs m) =
    (k * p).negOnePow • (((𝟙 _ ≫ N'.map x y).f p f).v l n (by omega)
      (((a x).f k t).v r l hl m)) at h
  simpa only [Category.id_comp, leftAction] using h

variable (D) [Small.{u} D]

/-- 左加群の主Hom評価族の全豊穣自然性。 -/
lemma leftModuleHomπ_naturality (N N' : LeftModule A D) (x y : D) :
    (β_ (leftModuleHom A D N N') (x ⟶[Complex A] y)).hom ≫
      (N.map x y ⊗ₘ leftModuleHomπ A D N N' y) ≫ enrichedComposition _ _ _ =
    (leftModuleHomπ A D N N' x ⊗ₘ N'.map x y) ≫ enrichedComposition _ _ _ := by
  have h := moduleHomπ_naturality A Dᵒᵖ N.toRightOpposite N'.toRightOpposite
    (op (op x)) (op (op y))
  change (β_ (leftModuleHom A D N N') (x ⟶[Complex A] y)).hom ≫
      ((𝟙 _ ≫ N.map x y) ⊗ₘ leftModuleHomπ A D N N' y) ≫ enrichedComposition _ _ _ =
    (leftModuleHomπ A D N N' x ⊗ₘ (𝟙 _ ≫ N'.map x y)) ≫ enrichedComposition _ _ _ at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
