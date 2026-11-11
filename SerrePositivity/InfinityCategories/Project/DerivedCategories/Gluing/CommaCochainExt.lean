module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaComparison

/-! 全次数の comma Hom cochain は、二射影と同じ第三 cochain で決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded

/-- mapping cocone への任意次数 cochain の二成分による一意性。 -/
lemma dgGluingCoconeCochain_ext {R : Type u} [CommRing R] {P Q K : Complex R}
    (d : P ⟶ Q) {p : ℤ} (f g : Cochain K (mappingCocone d) p)
    (hp : f.comp (Cochain.ofHom (mappingCocone.fst d)) (add_zero p) =
      g.comp (Cochain.ofHom (mappingCocone.fst d)) (add_zero p))
    (ht : f.comp (mappingCocone.snd d) (by omega : p + -1 = p - 1) =
      g.comp (mappingCocone.snd d) (by omega : p + -1 = p - 1)) : f = g := by
  apply Cochain.ext
  intro j k hjk
  have hpj := Cochain.congr_v hp j k hjk
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hpj
  have htj := Cochain.congr_v ht j (k - 1) (by omega)
  rw [Cochain.comp_v _ _ (by omega : p + -1 = p - 1) j k (k - 1) hjk (by omega),
    Cochain.comp_v _ _ (by omega : p + -1 = p - 1) j k (k - 1) hjk (by omega)] at htj
  have decomp (a : Cochain K (mappingCocone d) p) :
      a.v j k hjk = (a.v j k hjk ≫ (mappingCocone.fst d).f k) ≫
        (mappingCocone.inl d).v k k (add_zero k) +
      (a.v j k hjk ≫ (mappingCocone.snd d).v k (k - 1) (by omega)) ≫
        (mappingCocone.inr d).1.v (k - 1) k (by omega) := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      mappingCocone.id_X d k (k - 1) (by omega), Category.comp_id]
  rw [decomp f, decomp g, hpj, htj]

/-- 全次数の実 comma cochain の一意性。 -/
lemma dgGluingCommaCochain_ext (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (E : Type w) [DGCategory R E]
    (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
    {K : Complex R} {p : ℤ} (f g : Cochain K (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y) p)
    (ha : f.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y)) (add_zero p) =
      g.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y)) (add_zero p))
    (hb : f.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)) (add_zero p) =
      g.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)) (add_zero p))
    (ht : f.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y) (by omega : p + -1 = p - 1) =
      g.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y) (by omega : p + -1 = p - 1)) : f = g := by
  apply dgGluingCoconeCochain_ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) f g _ ht
  apply Cochain.ext
  intro j k hjk
  have hj := Cochain.congr_v ha j k hjk
  have hk := Cochain.congr_v hb j k hjk
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap,
    HomologicalComplex.comp_f] at hj hk
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  let S := homObject R C X.source Y.source
  let T := homObject R E X.replacement Y.replacement
  have htotal : biprod.fst ≫ (biprod.inl : S ⟶ S ⊞ T) +
      biprod.snd ≫ biprod.inr = 𝟙 (S ⊞ T) := biprod.total
  have htj := congrArg (fun a => a.f k) htotal
  simp only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
    HomologicalComplex.id_f] at htj
  have decomp (a : K.X j ⟶ (S ⊞ T).X k) :
      a = (a ≫ (biprod.fst : S ⊞ T ⟶ S).f k) ≫ (biprod.inl : S ⟶ S ⊞ T).f k +
        (a ≫ (biprod.snd : S ⊞ T ⟶ T).f k) ≫ (biprod.inr : T ⟶ S ⊞ T).f k := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, htj, Category.comp_id]
  erw [decomp (f.v j k hjk ≫
    (mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)).f k),
    decomp (g.v j k hjk ≫
      (mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)).f k), hj, hk]
  simp only [Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
