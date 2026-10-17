module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltration

/-! # 固定長 path 直和の射影と最終微分との整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
attribute [local instance] Classical.propDecidable

/-- 指定条件を満たす word の内部 path 項だけの直和。 -/
abbrev selectedHom (S : Set D) (P : Word S → Prop) (x y : D) : Complex A :=
  ∐ (fun w : {w : Word S // P w} => term A D w.val x y)

def selectedInclusion (S : Set D) (P : Word S → Prop) (x y : D) :
    selectedHom A D S P x y ⟶ internalHom A D S x y :=
  Sigma.desc (fun w => ι A D S x y w.val)

def selectedProjection (S : Set D) (P : Word S → Prop) (x y : D) :
    internalHom A D S x y ⟶ selectedHom A D S P x y := by
  classical
  exact Sigma.desc (fun w => if h : P w then
    Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) ⟨w, h⟩ else 0)

@[reassoc] lemma selected_ι_inclusion (S : Set D) (P : Word S → Prop) (x y : D)
    (w : {w : Word S // P w}) :
    Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) w ≫
      selectedInclusion A D S P x y = ι A D S x y w.val := Sigma.ι_comp_desc _ _

lemma ι_selectedProjection (S : Set D) (P : Word S → Prop) (x y : D) (w : Word S) :
    ι A D S x y w ≫ selectedProjection A D S P x y =
      if h : P w then
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) ⟨w, h⟩ else 0 := by
  classical
  exact Sigma.ι_comp_desc _ _

lemma selectedInclusion_projection (S : Set D) (P : Word S → Prop) (x y : D) :
    selectedInclusion A D S P x y ≫ selectedProjection A D S P x y = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro w
  rw [← Category.assoc, selected_ι_inclusion, ι_selectedProjection, dite_eq_left w.property,
    Category.comp_id]

/-- 指定した全 word の長さが n 以下なら、その直和の像は第 n 段階に属する。 -/
lemma selectedInclusion_mem_length (S : Set D) (P : Word S → Prop) (x y : D) (n : ℕ)
    (hP : ∀ w, P w → w.length ≤ n) (i : ℤ) (z : (selectedHom A D S P x y).X i) :
    (selectedInclusion A D S P x y).f i z ∈ lengthSubmodule A D S x y n i := by
  let F := lengthSubmodule A D S x y n i
  have hq : (selectedInclusion A D S P x y).f i ≫ ModuleCat.ofHom F.mkQ = 0 := by
    apply (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) i)
      (fun w : {w : Word S // P w} => term A D w.val x y)).hom_ext
    rintro ⟨w⟩
    have h := congrArg (fun f => f.f i) (selected_ι_inclusion A D S P x y w)
    simp only [HomologicalComplex.comp_f] at h
    change (Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x y) w).f i ≫
      ((selectedInclusion A D S P x y).f i ≫ ModuleCat.ofHom F.mkQ) = _
    rw [← Category.assoc, h]
    ext t
    exact (Submodule.Quotient.mk_eq_zero F).2
      (path_mem_lengthSubmodule A D S x y n i w.val (hP w.val w.property) t)
  apply (Submodule.Quotient.mk_eq_zero F).1
  exact congrArg (fun f => f z) hq

abbrev fixedLengthHom (S : Set D) (x y : D) (n : ℕ) : Complex A :=
  selectedHom A D S (fun w => w.length = n) x y

abbrev fixedLengthInclusion (S : Set D) (x y : D) (n : ℕ) :
    fixedLengthHom A D S x y n ⟶ internalHom A D S x y :=
  selectedInclusion A D S (fun w => w.length = n) x y

abbrev fixedLengthProjection (S : Set D) (x y : D) (n : ℕ) :
    internalHom A D S x y ⟶ fixedLengthHom A D S x y n :=
  selectedProjection A D S (fun w => w.length = n) x y

/-- 長さ n+1 への射影は n 以下の部分加群を消す。 -/
lemma fixedLengthProjection_kills_lower (S : Set D) (x y : D) (n : ℕ) (i : ℤ) :
    lengthSubmodule A D S x y n i ≤
      LinearMap.ker ((fixedLengthProjection A D S x y (n + 1)).f i).hom := by
  classical
  refine iSup_le (fun w => iSup_le (fun hw => ?_))
  rintro z ⟨t, rfl⟩
  have he : w.length ≠ n + 1 := by omega
  have h := congrArg (fun f => f.f i t)
    (ι_selectedProjection A D S (fun w => w.length = n + 1) x y w)
  simp only [dite_eq_right he, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    HomologicalComplex.zero_f] at h
  exact h

/-- 最終微分の消去部分は、固定長への射影の下で零となる。 -/
lemma fixedLengthProjection_erasure (S : Set D) (x y : D) (n : ℕ) (i : ℤ)
    (z : lengthSubmodule A D S x y (n + 1) i) :
    (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
      ((erasure A D S x y).v i (i + 1) rfl z.val) = 0 := by
  have hz := lengthSubmodule_erasure A D S x y (n + 1) i z.property
  exact fixedLengthProjection_kills_lower A D S x y n (i + 1) hz

/-- 最終微分を持つ第 n+1 段階から、内部微分だけの固定長直和への射影。 -/
def lengthLayerProjection (S : Set D) (x y : D) (n : ℕ) :
    lengthComplex A D S x y (n + 1) ⟶ fixedLengthHom A D S x y (n + 1) :=
  CochainComplex.ofHom (fun i =>
    ModuleCat.ofHom (lengthSubmodule A D S x y (n + 1) i).subtype ≫
      (fixedLengthProjection A D S x y (n + 1)).f i) (fun i => by
        rw [lengthComplex_d]
        ext z
        change (fixedLengthHom A D S x y (n + 1)).d i (i + 1)
          ((fixedLengthProjection A D S x y (n + 1)).f i z.val) =
          (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
            (lengthDifferential A D S x y (n + 1) i z).val
        rw [lengthDifferential_coe]
        have h := congrArg (fun f => f z.val)
          ((fixedLengthProjection A D S x y (n + 1)).comm i (i + 1))
        simp only [ModuleCat.comp_apply] at h
        rw [h]
        change (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
          ((internalHom A D S x y).d i (i + 1) z.val) =
          (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
            ((quotientHom A D S x y).d i (i + 1) z.val)
        rw [quotientHom_d]
        change _ = (fixedLengthProjection A D S x y (n + 1)).f (i + 1)
          ((internalHom A D S x y).d i (i + 1) z.val +
            (erasure A D S x y).v i (i + 1) rfl z.val)
        rw [map_add, fixedLengthProjection_erasure, add_zero])

end SerrePositivity.DifferentialGraded.DGQuotient
