module
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.HomFunctor

/-! # 主Homの自然性を斉次cochainの等式から構成する -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 四つの元の比較から作用と写像の可換式を得る。 -/
lemma element_square {X X' Y Y' : Type u} (a : X → Y) (b : X' → Y')
    (l : X → X') (r : Y → Y') (x : X) (x' : X') (y : Y) (y' : Y')
    (hl : l x = x') (ha : a x = y) (hb : b x' = y') (hr : r y = y') :
    b (l x) = r (a x) :=
  (congrArg b hl).trans (hb.trans (hr.symm.trans (congrArg r ha.symm)))

lemma cochain_comp_ofHom_apply {X Y Z : Complex A} {p i n : ℤ}
    (g : Cochain X Y p) (f : Y ⟶ Z) (hn : i + p = n) (x : X.X i) :
    (g.comp (Cochain.ofHom f) (add_zero p)).v i n hn x = f.f n (g.v i n hn x) := by
  rw [Cochain.comp_v _ _ _ i n n hn (add_zero n)]
  rfl

lemma cochain_ofHom_comp_apply {X Y Z : Complex A} {p i n : ℤ}
    (f : X ⟶ Y) (g : Cochain Y Z p) (hn : i + p = n) (x : X.X i) :
    ((Cochain.ofHom f).comp g (zero_add p)).v i n hn x = g.v i n hn (f.f i x) := by
  rw [Cochain.comp_v _ _ _ i i n (add_zero i) hn]
  rfl

lemma hom_naturality_of_apply {H X X' Y Y' : Complex A}
    (F : H ⟶ homComplex A X X') (G : H ⟶ homComplex A Y Y')
    (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : ∀ (p : ℤ) (g : H.X p),
      (F.f p g).comp (Cochain.ofHom b) (add_zero p) =
        (Cochain.ofHom a).comp (G.f p g) (zero_add p)) :
    F ≫ homPostcompose X b = G ≫ homPrecompose a Y' := by
  apply chain_ext_apply
  intro p g
  rw [chain_comp_apply, chain_comp_apply, homPostcompose_apply, homPrecompose_apply]
  exact h p g

end SerrePositivity.DifferentialGraded
