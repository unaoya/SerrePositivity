module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.EpsilonTensorSeparation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.QuotientWordSeparation
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：元 Hom の成分と独立な固定 ε の交換を、実 path 直和の成分で読む。
方針：単一語の生成式を用い、異なる語・異なる先頭次数を分離する。
規約：商関手の Hom 作用は作らず、ε 整合所属の必要条件だけを検証する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded DGQuotient
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set D)

/-- 左側の指定 ε との合成は、先頭次数零の単一語成分。 -/
lemma epsilon_original_left_word (x : S) (y : D) (q : ℤ)
    (z : (homObject R D x.val y).X q) :
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      (epsilonElement R D S x) ((originalHomInclusion R D S x.val y).f q z) rfl =
    (ι R D S x.val y [x]).f ((-1) + q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft R (homObject R D x.val x.val) (homObject R D x.val y)
        q (unitElement R x.val).val z) := by
  have h := path_inclusion_generator R D x [] x.val y 0 q ((-1) + q)
    (zero_add _) (unitElement R x.val).val z
  have hu : (originalHomInclusion R D S x.val x.val).f 0 (unitElement R x.val).val =
      (unitElement R (⟨x.val⟩ : QuotientObject D S)).val :=
    (inclusion R D S).map_unitElement R x.val
  let t : GradedHom R (⟨x.val⟩ : QuotientObject D S) ⟨y⟩ ((-1) + q) :=
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      (epsilonElement R D S x) ((originalHomInclusion R D S x.val y).f q z) rfl
  have hh := congrArg (fun a : GradedHom R (⟨x.val⟩ : QuotientObject D S) ⟨x.val⟩ 0 =>
    forward R (x := (⟨x.val⟩ : QuotientObject D S)) (y := ⟨x.val⟩) (z := ⟨y⟩)
      a t (zero_add _)) hu
  have he := forward_unit R (D := QuotientObject D S) t
  exact (hh.trans he).symm.trans h.symm

/-- 右側の指定 ε との合成は、先頭次数 q の単一語成分。 -/
lemma epsilon_original_right_word (x : D) (y : S) (q : ℤ)
    (z : (homObject R D x y.val).X q) :
    forward R (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨y.val⟩) (z := ⟨y.val⟩)
      ((originalHomInclusion R D S x y.val).f q z) (epsilonElement R D S y) (by omega) =
    (ι R D S x y.val [y]).f ((-1) + q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorRight R (homObject R D x y.val) (homObject R D y.val y.val)
        q z (unitElement R y.val).val) := by
  have h := path_inclusion_generator R D y [] x y.val q 0 ((-1) + q)
    (by omega) z (unitElement R y.val).val
  have hu : (originalHomInclusion R D S y.val y.val).f 0 (unitElement R y.val).val =
      (unitElement R (⟨y.val⟩ : QuotientObject D S)).val :=
    (inclusion R D S).map_unitElement R y.val
  have hh := congrArg (fun a : GradedHom R (⟨y.val⟩ : QuotientObject D S) ⟨y.val⟩ 0 =>
    forward R (x := (⟨y.val⟩ : QuotientObject D S)) (y := ⟨y.val⟩) (z := ⟨y.val⟩)
      (epsilonElement R D S y) a (add_zero _)) hu
  have hi := hh.trans (unit_forward R (D := QuotientObject D S) (x := ⟨y.val⟩) (y := ⟨y.val⟩)
    (n := (-1)) (epsilonElement R D S y))
  have he := congrArg (fun a : GradedHom R (⟨y.val⟩ : QuotientObject D S) ⟨y.val⟩ (-1) =>
    forward R (x := (⟨x⟩ : QuotientObject D S)) (y := ⟨y.val⟩) (z := ⟨y.val⟩)
      (n := (-1) + q) ((originalHomInclusion R D S x y.val).f q z) a (by omega)) hi
  exact he.symm.trans h.symm

/-- 非零次数、または異なる収縮対象を結ぶ元 Hom 成分は、固定 ε と交換すると零。 -/
lemma epsilon_original_component_zero
    (x y : S) (q : ℤ) (l : (homObject R D x.val x.val).X 0 →ₗ[R] R)
    (hl : l (unitElement R x.val).val = 1)
    (z : (homObject R D x.val y.val).X q) (hc : q ≠ 0 ∨ x.val ≠ y.val)
    (hε : forward R (x := (⟨x.val⟩ : QuotientObject D S))
      (y := ⟨x.val⟩) (z := ⟨y.val⟩) (epsilonElement R D S x)
        ((originalHomInclusion R D S x.val y.val).f q z) rfl =
      (q * (-1)).negOnePow • forward R (x := (⟨x.val⟩ : QuotientObject D S))
        (y := ⟨y.val⟩) (z := ⟨y.val⟩)
        ((originalHomInclusion R D S x.val y.val).f q z)
        (epsilonElement R D S y) (by omega)) : z = 0 := by
  rw [epsilon_original_left_word, epsilon_original_right_word] at hε
  rw [Units.smul_def] at hε
  rw [← map_zsmul ((ι R D S x.val y.val [y]).f ((-1) + q)).hom] at hε
  by_cases hxy : x = y
  · subst y
    have hq : q ≠ 0 := by simpa only [ne_self_iff_false, or_false] using hc
    have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientWordInclusion_injective R D S x.val x.val [x] ((-1) + q) hε
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorRight at he
    rw [← map_zsmul (ιTensorObj (homObject R D x.val x.val)
      (complexSphere R (-1) ⊗ homObject R D x.val x.val) q (-1) ((-1) + q) (by omega)).hom] at he
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft_eq_other_degree R (homObject R D x.val x.val)
      (homObject R D x.val x.val) q hq l (unitElement R x.val).val hl z _ he
  · have hw : ([y] : Word S) ≠ [x] := by
      intro h
      exact hxy (List.cons.inj h).1.symm
    have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgQuotientWord_separation R D S x.val y.val [x] [y] hw ((-1) + q) _ _ hε
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilonTensorLeft_eq_zero R (homObject R D x.val x.val)
      (homObject R D x.val y.val) q l (unitElement R x.val).val hl z ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
