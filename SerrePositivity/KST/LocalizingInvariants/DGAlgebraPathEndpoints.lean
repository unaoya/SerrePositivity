module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathModel

/-!
概要：実経路代数の二端点への全射性と、両評価間の鎖ホモトピーを供給する。
方針：mapping cocone の実第一射影と次数ごとの切断・比較 cochain を使う。
規約：二端点への射自体の準同型性は主張しない。使われ方：代数的経路比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

def endpointsHom : (algebra R B).X ⟶ B.X ⊞ B.X := mappingCocone.fst (difference R B)

lemma endpointsHom_fst : endpointsHom R B ≫ biprod.fst = (source R B).hom := rfl

lemma endpointsHom_snd : endpointsHom R B ≫ biprod.snd = (target R B).hom := rfl

lemma endpointsHom_surjective (n : ℤ) : Function.Surjective ((endpointsHom R B).f n) := by
  intro y
  refine ⟨(mappingCocone.inl (difference R B)).v n n (add_zero n) y, ?_⟩
  exact ConcreteCategory.congr_hom (mappingCocone.inl_v_fst_f (difference R B) n) y

lemma source_surjective (n : ℤ) : Function.Surjective ((source R B).hom.f n) := by
  have hs : (biprod.inl : B.X ⟶ B.X ⊞ B.X).f n ≫
      (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
        ((source R B).hom).f n = 𝟙 _ := by
    change (biprod.inl : B.X ⟶ B.X ⊞ B.X).f n ≫
      (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
        ((mappingCocone.fst (difference R B)).f n ≫ (biprod.fst : B.X ⊞ B.X ⟶ B.X).f n) = _
    rw [← Category.assoc ((mappingCocone.inl (difference R B)).v n n (add_zero n)),
      mappingCocone.inl_v_fst_f, Category.id_comp, ← HomologicalComplex.comp_f,
      biprod.inl_fst, HomologicalComplex.id_f]
  intro y
  refine ⟨(mappingCocone.inl (difference R B)).v n n (add_zero n)
    ((biprod.inl : B.X ⟶ B.X ⊞ B.X).f n y), ?_⟩
  exact ConcreteCategory.congr_hom hs y

lemma target_surjective (n : ℤ) : Function.Surjective ((target R B).hom.f n) := by
  have hs : (biprod.inr : B.X ⟶ B.X ⊞ B.X).f n ≫
      (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
        ((target R B).hom).f n = 𝟙 _ := by
    change (biprod.inr : B.X ⟶ B.X ⊞ B.X).f n ≫
      (mappingCocone.inl (difference R B)).v n n (add_zero n) ≫
        ((mappingCocone.fst (difference R B)).f n ≫ (biprod.snd : B.X ⊞ B.X ⟶ B.X).f n) = _
    rw [← Category.assoc ((mappingCocone.inl (difference R B)).v n n (add_zero n)),
      mappingCocone.inl_v_fst_f, Category.id_comp, ← HomologicalComplex.comp_f,
      biprod.inr_snd, HomologicalComplex.id_f]
  intro y
  refine ⟨(mappingCocone.inl (difference R B)).v n n (add_zero n)
    ((biprod.inr : B.X ⟶ B.X ⊞ B.X).f n y), ?_⟩
  exact ConcreteCategory.congr_hom hs y

lemma endpointsHom_difference : endpointsHom R B ≫ difference R B =
    (source R B).hom - (target R B).hom := by
  rw [difference_eq, Preadditive.comp_sub, endpointsHom_fst, endpointsHom_snd]

def endpointsHomotopy : Homotopy (source R B).hom (target R B).hom := by
  let h : Cochain (algebra R B).X B.X (-1) := mappingCocone.snd (difference R B)
  have hb : δ (-1) 0 h + Cochain.ofHom (endpointsHom R B ≫ difference R B) = 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary (difference R B)
  rw [endpointsHom_difference, Cochain.ofHom_sub] at hb
  refine (Cochain.equivHomotopy _ _).symm ⟨-h, ?_⟩
  rw [δ_neg, eq_neg_of_add_eq_zero_left hb, neg_neg]
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
