module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPrimitiveBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeBoundary

/-!
概要：経路代数への任意整数次数の cochain は両評価と比較成分で一意に決まる。
方針：mapping cocone の各次数の二射影による一意性を使う。
規約：chain map や閉 cochain に限定しない。使われ方：二重経路 connection の比較成分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma cochain_ext {K : Complex R} {n : ℤ} (f g : Cochain K (algebra R B).X n)
    (hs : f.comp (Cochain.ofHom (source R B).hom) (add_zero n) =
      g.comp (Cochain.ofHom (source R B).hom) (add_zero n))
    (ht : f.comp (Cochain.ofHom (target R B).hom) (add_zero n) =
      g.comp (Cochain.ofHom (target R B).hom) (add_zero n))
    (hp : f.comp (primitive R B) (by omega : n + -1 = n - 1) =
      g.comp (primitive R B) (by omega : n + -1 = n - 1)) : f = g := by
  apply Cochain.ext
  intro p q hpq
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_X_ext (difference R B) q
  · have total := congrArg (fun k => k.f q)
      (biprod.total (X := B.X) (Y := B.X))
    have hsource := Cochain.congr_v hs p q hpq
    have htarget := Cochain.congr_v ht p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hsource htarget
    have decomp (a : K.X p ⟶ (B.X ⊞ B.X).X q) :
        a = (a ≫ (biprod.fst : B.X ⊞ B.X ⟶ B.X).f q) ≫ (biprod.inl : B.X ⟶ B.X ⊞ B.X).f q +
          (a ≫ (biprod.snd : B.X ⊞ B.X ⟶ B.X).f q) ≫ (biprod.inr : B.X ⟶ B.X ⊞ B.X).f q := by
      simpa only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, Preadditive.comp_add, Category.comp_id,
        Category.assoc] using congrArg (fun k => a ≫ k) total.symm
    have hs' : f.v p q hpq ≫ (mappingCocone.fst (difference R B)).f q ≫
        (biprod.fst : B.X ⊞ B.X ⟶ B.X).f q =
        g.v p q hpq ≫ (mappingCocone.fst (difference R B)).f q ≫
          (biprod.fst : B.X ⊞ B.X ⟶ B.X).f q := by
      simpa only [source, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap, difference,
        HomologicalComplex.comp_f, Category.assoc] using! hsource
    have ht' : f.v p q hpq ≫ (mappingCocone.fst (difference R B)).f q ≫
        (biprod.snd : B.X ⊞ B.X ⟶ B.X).f q =
        g.v p q hpq ≫ (mappingCocone.fst (difference R B)).f q ≫
          (biprod.snd : B.X ⊞ B.X ⟶ B.X).f q := by
      simpa only [target, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap, difference,
        HomologicalComplex.comp_f, Category.assoc] using! htarget
    calc
      _ = _ := decomp (f.v p q hpq ≫ (mappingCocone.fst (difference R B)).f q)
      _ = _ := by simp only [Category.assoc, hs', ht']
      _ = _ := (decomp (g.v p q hpq ≫
        (mappingCocone.fst (difference R B)).f q)).symm
  · have h := Cochain.congr_v hp p (q - 1) (by omega)
    rw [Cochain.comp_v f (primitive R B) _ p q (q - 1) hpq (by omega),
      Cochain.comp_v g (primitive R B) _ p q (q - 1) hpq (by omega)] at h
    exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
