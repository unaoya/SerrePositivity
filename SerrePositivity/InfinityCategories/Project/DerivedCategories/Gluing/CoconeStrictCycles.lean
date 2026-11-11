module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBoundary
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! 差写像が零になる任意次数の閉元を、第三成分零の同じ cocone 閉元へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {P Q : Complex R} (d : P ⟶ Q) (n : ℤ) (a : P.X n)

/-- 同じ次数の元を、cocone の第三成分零の包含へ入れる。 -/
def dgGluingCoconeStrictElement : (mappingCocone d).X n :=
  (mappingCocone.inl d).v n n (add_zero n) a

/-- 第一射影は、元の同じ斉次元を厳密に回収。 -/
lemma dgGluingCoconeStrictElement_fst :
    (mappingCocone.fst d).f n (dgGluingCoconeStrictElement d n a) = a :=
  congrArg (fun f => f a) (mappingCocone.inl_v_fst_f d n)

/-- 第三成分は、同じ次数の零元。 -/
lemma dgGluingCoconeStrictElement_snd :
    (mappingCocone.snd d).v n (n - 1) (by omega)
      (dgGluingCoconeStrictElement d n a) = 0 :=
  congrArg (fun f => f a) (mappingCocone.inl_v_snd_v d n (n - 1) (by omega))

/-- 元が閉じ、差写像で零になるなら、同じ第三成分零の持ち上げも閉じる。 -/
lemma dgGluingCoconeStrictElement_closed
    (ha : P.d n (n + 1) a = 0) (hd : d.f n a = 0) :
    (mappingCocone d).d n (n + 1) (dgGluingCoconeStrictElement d n a) = 0 := by
  let x := dgGluingCoconeStrictElement d n a
  have hf := congrArg (fun f => f x) ((mappingCocone.fst d).comm n (n + 1))
  dsimp only [x] at hf
  simp only [ModuleCat.comp_apply, dgGluingCoconeStrictElement_fst, ha] at hf
  have hs := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary d) n n (add_zero n)
  rw [Cochain.add_v, δ_v (-1) 0 (by omega) (mappingCocone.snd d)
    n n (add_zero n) (n - 1) (n + 1) (by omega) (by omega), Cochain.ofHom_v] at hs
  have hs' := congrArg (fun f => f x) hs
  dsimp only [x] at hs'
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    Int.negOnePow_zero, one_smul, HomologicalComplex.comp_f,
    dgGluingCoconeStrictElement_snd, dgGluingCoconeStrictElement_fst,
    map_zero, hd, zero_add, add_zero, Cochain.zero_v, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hs'
  have hi := congrArg (fun f => f ((mappingCocone d).d n (n + 1) x))
    (mappingCocone.id_X d (n + 1) n (by omega))
  dsimp only [x] at hi
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
    ← hf, hs', map_zero, zero_add, ModuleCat.id_apply] at hi
  exact hi.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
