module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaHomExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaComparison

/-! 実 comma Hom の任意次数の元は、二射影と第三成分で厳密に決まる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) (n : ℤ)

/-- 全次数の同じ三成分による、実斉次 comma 元の一意性。 -/
lemma dgGluingCommaElement_ext
    (f g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y).X n)
    (ha : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y).f n f =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y).f n g)
    (hb : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f n f =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f n g)
    (ht : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega) f =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).v n (n - 1) (by omega) g) : f = g := by
  let P := homObject R C X.source Y.source
  let Q := homObject R E X.replacement Y.replacement
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y
  have total := congrArg (fun k => k.f n) (biprod.total (X := P) (Y := Q))
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at total
  have bp (x : (P ⊞ Q).X n) :
      (biprod.inl : P ⟶ P ⊞ Q).f n ((biprod.fst : P ⊞ Q ⟶ P).f n x) +
        (biprod.inr : Q ⟶ P ⊞ Q).f n ((biprod.snd : P ⊞ Q ⟶ Q).f n x) = x := by
    have h := congrArg (fun k => k x) total
    simpa only [ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.comp_apply, ModuleCat.id_apply] using h
  have hp : (mappingCocone.fst d).f n f = (mappingCocone.fst d).f n g := by
    rw [← bp ((mappingCocone.fst d).f n f), ← bp ((mappingCocone.fst d).f n g)]
    change _ + _ = _ + _
    change (biprod.inl : P ⟶ P ⊞ Q).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y).f n f) +
      (biprod.inr : Q ⟶ P ⊞ Q).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f n f) =
      (biprod.inl : P ⟶ P ⊞ Q).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y).f n g) +
      (biprod.inr : Q ⟶ P ⊞ Q).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y).f n g)
    rw [ha, hb]
  have dec (x : (mappingCocone d).X n) :
      (mappingCocone.inl d).v n n (add_zero n) ((mappingCocone.fst d).f n x) +
        (mappingCocone.inr d).1.v (n - 1) n (by omega)
          ((mappingCocone.snd d).v n (n - 1) (by omega) x) = x := by
    have h := congrArg (fun k => k x) (mappingCocone.id_X d n (n - 1) (by omega))
    simpa only [ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.comp_apply, ModuleCat.id_apply] using h
  change (mappingCocone.snd d).v n (n - 1) (by omega) f =
    (mappingCocone.snd d).v n (n - 1) (by omega) g at ht
  rw [← dec f, ← dec g, hp, ht]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
