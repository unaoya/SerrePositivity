module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeMap
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
概要：次数全射な可換正方形は、mapping cocone の各次数でも全射を誘導する。
方針：実二射影の値を別々に持ち上げ、実 cocone の斉次二包含で組み立てる。
規約：ホモロジーの全射性では代用しない。使われ方：相対経路の実射の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma cochainMappingCocone_element_ext {K L : Complex R} (d : K ⟶ L) (n : ℤ)
    {x y : (mappingCocone d).X n}
    (h₁ : (mappingCocone.fst d).f n x = (mappingCocone.fst d).f n y)
    (h₂ : (mappingCocone.snd d).v n (n - 1) (by omega) x =
      (mappingCocone.snd d).v n (n - 1) (by omega) y) : x = y := by
  have hx := ConcreteCategory.congr_hom (mappingCocone.id_X d n (n - 1) (by omega)) x
  have hy := ConcreteCategory.congr_hom (mappingCocone.id_X d n (n - 1) (by omega)) y
  change (mappingCocone.inl d).v n n (add_zero n) ((mappingCocone.fst d).f n x) +
    (mappingCocone.inr d).1.v (n - 1) n (by omega)
      ((mappingCocone.snd d).v n (n - 1) (by omega) x) = x at hx
  change (mappingCocone.inl d).v n n (add_zero n) ((mappingCocone.fst d).f n y) +
    (mappingCocone.inr d).1.v (n - 1) n (by omega)
      ((mappingCocone.snd d).v n (n - 1) (by omega) y) = y at hy
  rw [h₁, h₂] at hx
  exact hx.symm.trans hy

lemma cochainMappingCoconeMap_surjective {K₁ L₁ K₂ L₂ : Complex R}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : d₁ ≫ b = a ≫ d₂) (n : ℤ)
    (ha : Function.Surjective (a.f n)) (hb : Function.Surjective (b.f (n - 1))) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b comm).f n) := by
  intro y
  obtain ⟨x₁, hx₁⟩ := ha ((mappingCocone.fst d₂).f n y)
  obtain ⟨x₂, hx₂⟩ := hb ((mappingCocone.snd d₂).v n (n - 1) (by omega) y)
  let x : (mappingCocone d₁).X n :=
    (mappingCocone.inl d₁).v n n (add_zero n) x₁ +
      (mappingCocone.inr d₁).1.v (n - 1) n (by omega) x₂
  have hf : (mappingCocone.fst d₁).f n x = x₁ := by
    have hi := ConcreteCategory.congr_hom (mappingCocone.inl_v_fst_f d₁ n) x₁
    have hj := ConcreteCategory.congr_hom
      (mappingCocone.inr_v_fst_f d₁ (n - 1) n (by omega)) x₂
    change (mappingCocone.fst d₁).f n
      ((mappingCocone.inl d₁).v n n (add_zero n) x₁) = x₁ at hi
    change (mappingCocone.fst d₁).f n
      ((mappingCocone.inr d₁).1.v (n - 1) n (by omega) x₂) = 0 at hj
    change (mappingCocone.fst d₁).f n (_ + _) = _
    rw [map_add, hi, hj, add_zero]
  have hs : (mappingCocone.snd d₁).v n (n - 1) (by omega) x = x₂ := by
    have hi := ConcreteCategory.congr_hom
      (mappingCocone.inl_v_snd_v d₁ n (n - 1) (by omega)) x₁
    have hj := ConcreteCategory.congr_hom
      (mappingCocone.inr_v_snd_v d₁ (n - 1) n (by omega)) x₂
    change (mappingCocone.snd d₁).v n (n - 1) (by omega)
      ((mappingCocone.inl d₁).v n n (add_zero n) x₁) = 0 at hi
    change (mappingCocone.snd d₁).v n (n - 1) (by omega)
      ((mappingCocone.inr d₁).1.v (n - 1) n (by omega) x₂) = x₂ at hj
    change (mappingCocone.snd d₁).v n (n - 1) (by omega) (_ + _) = _
    rw [map_add, hi, hj, zero_add]
  refine ⟨x, cochainMappingCocone_element_ext d₂ n ?_ ?_⟩
  · have he := ConcreteCategory.congr_hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_fst_f d₁ d₂ a b comm n) x
    change (mappingCocone.fst d₂).f n
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b comm).f n x) =
        a.f n ((mappingCocone.fst d₁).f n x) at he
    exact he.trans ((congrArg (a.f n) hf).trans hx₁)
  · have he := ConcreteCategory.congr_hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_f_snd_v d₁ d₂ a b comm n (n - 1) (by omega)) x
    change (mappingCocone.snd d₂).v n (n - 1) (by omega)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap d₁ d₂ a b comm).f n x) =
        b.f (n - 1) ((mappingCocone.snd d₁).v n (n - 1) (by omega) x) at he
    exact he.trans ((congrArg (b.f (n - 1)) hs).trans hx₂)

end SerrePositivity.KST.LocalizingInvariants
