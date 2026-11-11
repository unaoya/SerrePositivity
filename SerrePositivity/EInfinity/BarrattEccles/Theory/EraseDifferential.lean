module

public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# 微分を消した複体のテンソルと余極限

## 概要
Berger–Moerdijk 命題 4.1 のセル付加を、次数付きの台で計算するための複体の比較。

## 方針
元の加群と射の次数成分を使い、テンソルの各斉次成分と点ごとの余極限を照合する。

## 規約
整数添字の余鎖複体と Koszul 符号を用いる。

## 使われ方
セル付加の次数付き自由表示。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex
open DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 複体の次数成分を保って微分を零にする。 -/
def eraseDifferential : Complex A ⥤ Complex A where
  obj K :=
    { X := K.X
      d := fun _ _ => 0
      shape := by simp
      d_comp_d' := by simp }
  map f :=
    { f := f.f
      comm' := by
        intro i j h
        simp }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma eraseDifferential_d (K : Complex A) (i j : ℤ) :
    ((eraseDifferential A).obj K).d i j = 0 := rfl

/-- 微分が零の二複体のテンソルも微分が零。 -/
lemma tensor_d_eq_zero_of_d_eq_zero {K L : Complex A}
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) (i j : ℤ) :
    (K ⊗ L).d i j = 0 := by
  by_cases h : i + 1 = j
  · subst j
    apply mapBifunctor.hom_ext
    intro p q hpq
    change ιTensorObj K L p q i hpq ≫ (cochainTensor K L).d i (i + 1) =
      ιTensorObj K L p q i hpq ≫ 0
    rw [ιTensorObj_cochainTensor_d]
    simp [hK, hL]
  · exact (K ⊗ L).shape i j h

/-- テンソルの次数付き加群は因子の微分に依存しない。 -/
theorem eraseDifferentialTensor_eq (K L : Complex A) :
    (eraseDifferential A).obj K ⊗ (eraseDifferential A).obj L =
      (eraseDifferential A).obj (K ⊗ L) := by
  refine HomologicalComplex.ext (by rfl) ?_
  intro i j h
  rw [eraseDifferential_d, tensor_d_eq_zero_of_d_eq_zero A
    (eraseDifferential_d A K) (eraseDifferential_d A L)]
  simp

/-- 次数付きテンソルの比較同型。 -/
def eraseDifferentialTensorIso (K L : Complex A) :
    (eraseDifferential A).obj K ⊗ (eraseDifferential A).obj L ≅
      (eraseDifferential A).obj (K ⊗ L) :=
  { hom :=
      { f := fun _ => 𝟙 _
        comm' := by
          intro i j h
          rw [eraseDifferential_d, tensor_d_eq_zero_of_d_eq_zero A
            (eraseDifferential_d A K) (eraseDifferential_d A L)]
          simp }
    inv :=
      { f := fun _ => 𝟙 _
        comm' := by
          intro i j h
          rw [eraseDifferential_d, tensor_d_eq_zero_of_d_eq_zero A
            (eraseDifferential_d A K) (eraseDifferential_d A L)]
          simp }
    hom_inv_id := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact Category.id_comp _
    inv_hom_id := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact Category.id_comp _ }

@[simp]
lemma eraseDifferentialTensorIso_hom_f (K L : Complex A) (i : ℤ) :
    (eraseDifferentialTensorIso A K L).hom.f i = 𝟙 _ := by
  rfl

instance eraseDifferential_preservesZeroMorphisms :
    (eraseDifferential A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- 微分を零にする操作は点ごとの余極限を保つ。 -/
instance eraseDifferential_preservesColimitsOfShape {J : Type u} [Category.{u} J] :
    PreservesColimitsOfShape J (eraseDifferential A) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i =>
    inferInstanceAs (PreservesColimitsOfShape J
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i)))

@[simp]
lemma eraseDifferential_map_f {K L : Complex A} (f : K ⟶ L) (i : ℤ) :
    ((eraseDifferential A).map f).f i = f.f i := rfl

/-- テンソル単位はもともと微分零。 -/
theorem eraseDifferentialUnit_eq :
    𝟙_ (Complex A) = (eraseDifferential A).obj (𝟙_ (Complex A)) := by
  refine HomologicalComplex.ext (by rfl) ?_
  intro i j h
  have hd : (𝟙_ (Complex A)).d i j = 0 :=
    HomologicalComplex.single_obj_d (c := .up ℤ) 0 (𝟙_ (ModuleCat A)) i j
  rw [eraseDifferential_d, hd, zero_comp, comp_zero]

/-- テンソル単位の次数付き比較同型。 -/
def eraseDifferentialUnitIso :
    𝟙_ (Complex A) ≅ (eraseDifferential A).obj (𝟙_ (Complex A)) :=
  eqToIso (eraseDifferentialUnit_eq A)

@[simp]
lemma eraseDifferentialUnitIso_hom_f (i : ℤ) :
    (eraseDifferentialUnitIso A).hom.f i = 𝟙 _ := by
  rw [eraseDifferentialUnitIso, eqToIso.hom, eqToHom_f]
  rfl


end SerrePositivity.EInfinity
