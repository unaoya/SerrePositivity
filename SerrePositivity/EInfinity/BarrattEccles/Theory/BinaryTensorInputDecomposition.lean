module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColors
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorAction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorBicone
public import SerrePositivity.EInfinity.BarrattEccles.Theory.RepresentationComplex
public import SerrePositivity.EInfinity.Operad.TensorFamilyAdjacentTail
public import Mathlib.GroupTheory.Perm.Fin

/-!
# 指定包含と色付きテンソルの入力分解

## 概要
HA 3.2.4.7 の自由代数の指定比較に必要な色付き入力の補題。

## 方針
有限テンソル族との同定、任意の置換、安定化群の作用、直交する行列成分をまとめる。

## 規約
任意の入力複体の微分を保ち、既存の指定包含と指定置換を使う。

## 使われ方
色付き Schur 分解から二色の係数比較への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

section BinaryTensorFamily
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 色に対応する入力の複体。 -/
def binaryTensorColorObj : Bool → Complex A
  | false => X
  | true => Y

/-- 色の入力から和への指定包含。 -/
def binaryTensorColorInclusion : ∀ b, binaryTensorColorObj X Y b ⟶ X ⊞ Y
  | false => biprod.inl
  | true => biprod.inr

/-- 再帰的な入力語のテンソルを、色の有限族のテンソルへ同定する。 -/
def binaryTensorWordFamilyIso : ∀ n (w : BinaryTensorWord n),
    binaryTensorWordObj X Y n w ≅
      tensorFamily n (fun i => binaryTensorColorObj X Y (binaryTensorWordColors n w i))
  | 0, _ => Iso.refl _
  | n + 1, .inl w => whiskerLeftIso X (binaryTensorWordFamilyIso n w)
  | n + 1, .inr w => whiskerLeftIso Y (binaryTensorWordFamilyIso n w)

/-- 語の指定包含は、有限族の指定生成射に一致する。 -/
lemma binaryTensorWordFamilyIso_inclusion : ∀ n (w : BinaryTensorWord n),
    (binaryTensorWordFamilyIso X Y n w).hom ≫
      tensorFamilyGenerator (X ⊞ Y) (binaryTensorColorObj X Y)
        (binaryTensorColorInclusion X Y) n (binaryTensorWordColors n w) =
      binaryTensorWordInclusion X Y n w := by
  intro n
  induction n with
  | zero => intro w; exact Category.id_comp _
  | succ n ih =>
    intro w
    cases w with
    | inl w =>
      change (X ◁ (binaryTensorWordFamilyIso X Y n w).hom) ≫
        (biprod.inl ⊗ₘ tensorFamilyGenerator _ _ _ n (binaryTensorWordColors n w)) =
          biprod.inl ⊗ₘ binaryTensorWordInclusion X Y n w
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, ih]
    | inr w =>
      change (Y ◁ (binaryTensorWordFamilyIso X Y n w).hom) ≫
        (biprod.inr ⊗ₘ tensorFamilyGenerator _ _ _ n (binaryTensorWordColors n w)) =
          biprod.inr ⊗ₘ binaryTensorWordInclusion X Y n w
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, ih]

end SerrePositivity.EInfinity
end BinaryTensorFamily

section BinaryTensorAdjacent
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 隣接交換した語の色は、元の色を同じ隣接交換で引き戻したもの。 -/
lemma binaryTensorWordColors_adjacent (n : ℕ) (i : Fin n)
    (w : BinaryTensorWord (n + 1)) :
    (fun j => binaryTensorWordColors (n + 1) w (adjacentTransposition i j)) =
      binaryTensorWordColors (n + 1) (adjacentTransposition i • w) := by
  funext j
  rw [binaryTensorWordColors_smul]
  rfl

/-- 色の関数を等式で移した有限テンソル族の生成射の照合。 -/
lemma binaryTensorGenerator_index_eq {n : ℕ} {s t : Fin n → Bool} (h : s = t) :
    eqToHom (congrArg (fun s => tensorFamily n (fun j => binaryTensorColorObj X Y (s j))) h) ≫
      tensorFamilyGenerator (X ⊞ Y) (binaryTensorColorObj X Y)
        (binaryTensorColorInclusion X Y) n t =
      tensorFamilyGenerator (X ⊞ Y) (binaryTensorColorObj X Y)
        (binaryTensorColorInclusion X Y) n s := by
  subst t
  simp

/-- 語の隣接交換の指定同型。 -/
def binaryTensorWordAdjacentIso (n : ℕ) (i : Fin n) (w : BinaryTensorWord (n + 1)) :
    binaryTensorWordObj X Y (n + 1) w ≅
      binaryTensorWordObj X Y (n + 1) (adjacentTransposition i • w) :=
  binaryTensorWordFamilyIso X Y (n + 1) w ≪≫
    tensorFamilyAdjacentIso n
      (fun j => binaryTensorColorObj X Y (binaryTensorWordColors (n + 1) w j)) i ≪≫
    eqToIso (congrArg (fun s => tensorFamily (n + 1)
      (fun j => binaryTensorColorObj X Y (s j))) (binaryTensorWordColors_adjacent n i w)) ≪≫
    (binaryTensorWordFamilyIso X Y (n + 1) (adjacentTransposition i • w)).symm

/-- 隣接交換は、元のテンソル冪の隣接交換と指定包含の上で一致する。 -/
lemma binaryTensorWordAdjacentIso_inclusion (n : ℕ) (i : Fin n)
    (w : BinaryTensorWord (n + 1)) :
    (binaryTensorWordAdjacentIso X Y n i w).hom ≫
      binaryTensorWordInclusion X Y (n + 1) (adjacentTransposition i • w) =
      binaryTensorWordInclusion X Y (n + 1) w ≫ (adjacentIso (X ⊞ Y) n i).hom := by
  rw [← binaryTensorWordFamilyIso_inclusion X Y (n + 1) (adjacentTransposition i • w)]
  simp only [binaryTensorWordAdjacentIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [binaryTensorGenerator_index_eq X Y (binaryTensorWordColors_adjacent n i w)]
  have h := tensorFamilyAdjacentIso_generator (X ⊞ Y) n
    (fun j => binaryTensorColorObj X Y (binaryTensorWordColors (n + 1) w j))
    (fun j => binaryTensorColorInclusion X Y (binaryTensorWordColors (n + 1) w j)) i
  have hh : (tensorFamilyAdjacentIso n
      (fun j => binaryTensorColorObj X Y (binaryTensorWordColors (n + 1) w j)) i).hom ≫
      tensorFamilyGenerator (X ⊞ Y) (binaryTensorColorObj X Y)
        (binaryTensorColorInclusion X Y) (n + 1)
        (fun j => binaryTensorWordColors (n + 1) w (adjacentTransposition i j)) =
      tensorFamilyGenerator (X ⊞ Y) (binaryTensorColorObj X Y)
        (binaryTensorColorInclusion X Y) (n + 1) (binaryTensorWordColors (n + 1) w) ≫
          (adjacentIso (X ⊞ Y) n i).hom := by
    have hid := tensorFamilyGenerator_reindex (X ⊞ Y) (binaryTensorColorObj X Y)
      (binaryTensorColorInclusion X Y) (binaryTensorWordColors (n + 1) w)
      (n + 1) (fun j => j)
    rw [← hid] at h
    simpa only [tensorFamilyGenerator_reindex] using h
  rw [hh, ← Category.assoc, binaryTensorWordFamilyIso_inclusion]

end SerrePositivity.EInfinity
end BinaryTensorAdjacent

section BinaryTensorPermutations
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 語の等式に沿った移送は指定包含を保つ。 -/
lemma binaryTensorWordInclusion_word_eq {n : ℕ} {w z : BinaryTensorWord n} (h : w = z) :
    eqToHom (congrArg (binaryTensorWordObj X Y n) h) ≫
      binaryTensorWordInclusion X Y n z = binaryTensorWordInclusion X Y n w := by
  subst z
  simp

/-- 実際のテンソル冪の置換は、置換した語のテンソルへの同型に制限できる。 -/
lemma binaryTensorWord_exists_transport (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∀ w : BinaryTensorWord n,
      ∃ e : binaryTensorWordObj X Y n w ≅ binaryTensorWordObj X Y n (σ • w),
        e.hom ≫ binaryTensorWordInclusion X Y n (σ • w) =
          binaryTensorWordInclusion X Y n w ≫ (permutationAction (X ⊞ Y) n σ).asIso.hom := by
  have hone (r : ℕ) : ∀ w : BinaryTensorWord r,
      ∃ e : binaryTensorWordObj X Y r w ≅ binaryTensorWordObj X Y r ((1 : Equiv.Perm (Fin r)) • w),
        e.hom ≫ binaryTensorWordInclusion X Y r (1 • w) =
          binaryTensorWordInclusion X Y r w ≫ (permutationAction (X ⊞ Y) r 1).asIso.hom := by
    intro w
    refine ⟨eqToIso (congrArg (binaryTensorWordObj X Y r) (one_smul _ w).symm), ?_⟩
    rw [eqToIso.hom, binaryTensorWordInclusion_word_eq X Y (one_smul _ w).symm,
      permutationAction_one, Category.comp_id]
  cases n with
  | zero =>
    have h : σ = 1 := Subsingleton.elim _ _
    subst σ
    exact hone 0
  | succ n =>
    have hσ : σ ∈ Submonoid.closure (Set.range (@adjacentTransposition n)) := by
      rw [show (@adjacentTransposition n) =
        (fun i : Fin n => Equiv.swap i.castSucc i.succ) from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem τ hτ =>
      obtain ⟨i, rfl⟩ := hτ
      intro w
      refine ⟨binaryTensorWordAdjacentIso X Y n i w, ?_⟩
      rw [binaryTensorWordAdjacentIso_inclusion, permutationAction_adjacent]
      rfl
    | one => exact hone (n + 1)
    | mul σ τ _ _ hσ hτ =>
      intro w
      obtain ⟨eτ, heτ⟩ := hτ w
      obtain ⟨eσ, heσ⟩ := hσ (τ • w)
      refine ⟨eτ ≪≫ eσ ≪≫ eqToIso (congrArg (binaryTensorWordObj X Y (n + 1))
        (mul_smul σ τ w).symm), ?_⟩
      simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
      rw [binaryTensorWordInclusion_word_eq X Y (mul_smul σ τ w).symm,
        heσ, ← Category.assoc, heτ,
        Category.assoc, permutationAction_mul]

/-- 指定包含に沿って実際の置換を制限した、語のテンソルの同型。 -/
def binaryTensorWordPermutationIso (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) :
    binaryTensorWordObj X Y n w ≅ binaryTensorWordObj X Y n (σ • w) :=
  Classical.choose (binaryTensorWord_exists_transport X Y n σ w)

/-- 選択した同型は実際のテンソル冪の置換と指定包含の上で一致する。 -/
lemma binaryTensorWordPermutationIso_inclusion (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) :
    (binaryTensorWordPermutationIso X Y n σ w).hom ≫
      binaryTensorWordInclusion X Y n (σ • w) =
      binaryTensorWordInclusion X Y n w ≫ (permutationAction (X ⊞ Y) n σ).asIso.hom :=
  Classical.choose_spec (binaryTensorWord_exists_transport X Y n σ w)

/-- 同型の順射は、元の置換の指定包含と指定射影による成分である。 -/
lemma binaryTensorWordPermutationIso_hom (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w : BinaryTensorWord n) :
    (binaryTensorWordPermutationIso X Y n σ w).hom =
      binaryTensorWordInclusion X Y n w ≫ (permutationAction (X ⊞ Y) n σ).asIso.hom ≫
        binaryTensorWordProjection X Y n (σ • w) := by
  rw [← Category.assoc, ← binaryTensorWordPermutationIso_inclusion, Category.assoc,
    binaryTensorWordInclusion_projection, Category.comp_id]

end SerrePositivity.EInfinity
end BinaryTensorPermutations

section BinaryTensorFixedAction
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 指定包含の後で一致する射は、語のテンソルへの射として一致する。 -/
lemma binaryTensorWordInclusion_cancel {n : ℕ} (w : BinaryTensorWord n) {Z : Complex A}
    {f g : Z ⟶ binaryTensorWordObj X Y n w}
    (h : f ≫ binaryTensorWordInclusion X Y n w =
      g ≫ binaryTensorWordInclusion X Y n w) : f = g := by
  have hh := congrArg (fun k => k ≫ binaryTensorWordProjection X Y n w) h
  simpa only [Category.assoc, binaryTensorWordInclusion_projection, Category.comp_id] using hh

/-- 語を固定する置換の、その語の複体への指定制限。 -/
def binaryTensorWordFixedIso (n : ℕ) (w : BinaryTensorWord n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ • w = w) :
    binaryTensorWordObj X Y n w ≅ binaryTensorWordObj X Y n w :=
  binaryTensorWordPermutationIso X Y n σ w ≪≫
    eqToIso (congrArg (binaryTensorWordObj X Y n) hσ)

/-- 固定する置換の制限は、元のテンソル冪の作用と指定包含で一致する。 -/
@[reassoc]
lemma binaryTensorWordFixedIso_inclusion (n : ℕ) (w : BinaryTensorWord n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ • w = w) :
    (binaryTensorWordFixedIso X Y n w σ hσ).hom ≫
      binaryTensorWordInclusion X Y n w =
      binaryTensorWordInclusion X Y n w ≫ (permutationAction (X ⊞ Y) n σ).asIso.hom := by
  simp only [binaryTensorWordFixedIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [binaryTensorWordInclusion_word_eq X Y hσ, binaryTensorWordPermutationIso_inclusion]

/-- 語を固定する群は、その語のテンソル複体に作用する。 -/
def binaryTensorWordFixedAction {G : Type u} [Group G] (n : ℕ) (w : BinaryTensorWord n)
    (φ : G →* Equiv.Perm (Fin n)) (hφ : ∀ g, φ g • w = w) :
    G →* End (binaryTensorWordObj X Y n w) where
  toFun g := .of (binaryTensorWordFixedIso X Y n w (φ g) (hφ g)).hom
  map_one' := by
    apply End.ext
    apply binaryTensorWordInclusion_cancel X Y w
    change (binaryTensorWordFixedIso X Y n w (φ 1) (hφ 1)).hom ≫ _ = 𝟙 _ ≫ _
    rw [binaryTensorWordFixedIso_inclusion, map_one, permutationAction_one,
      Category.comp_id, Category.id_comp]
  map_mul' g h := by
    apply End.ext
    apply binaryTensorWordInclusion_cancel X Y w
    change (binaryTensorWordFixedIso X Y n w (φ (g * h)) (hφ (g * h))).hom ≫ _ =
      ((binaryTensorWordFixedIso X Y n w (φ h) (hφ h)).hom ≫
        (binaryTensorWordFixedIso X Y n w (φ g) (hφ g)).hom) ≫ _
    simp only [Category.assoc, binaryTensorWordFixedIso_inclusion_assoc,
      binaryTensorWordFixedIso_inclusion, map_mul]
    rfl

/-- 語を固定する群の実際の入力表現を、全整数次数の複体として読む。 -/
def binaryTensorWordFixedRepresentation {G : Type u} [Group G]
    (n : ℕ) (w : BinaryTensorWord n) (φ : G →* Equiv.Perm (Fin n))
    (hφ : ∀ g, φ g • w = w) : CochainComplex (Rep.{u} A G) ℤ :=
  representationCochainComplex (binaryTensorWordFixedAction X Y n w φ hφ)

end SerrePositivity.EInfinity
end BinaryTensorFixedAction

section BinaryTensorMatrix
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 置換した色の語と異なる成分への行列成分は零射。 -/
lemma binaryTensorWordPermutation_component_ne (n : ℕ) (σ : Equiv.Perm (Fin n))
    (w z : BinaryTensorWord n) (hz : σ • w ≠ z) :
    binaryTensorWordInclusion X Y n w ≫ (permutationAction (X ⊞ Y) n σ).asIso.hom ≫
      binaryTensorWordProjection X Y n z = 0 := by
  rw [← Category.assoc, ← binaryTensorWordPermutationIso_inclusion, Category.assoc,
    binaryTensorWordInclusion_projection_ne X Y n (σ • w) z hz, comp_zero]

/-- 固定する語への射影は、その語に制限した置換作用と可換。 -/
lemma binaryTensorWordFixedIso_projection (n : ℕ) (w : BinaryTensorWord n)
    (σ : Equiv.Perm (Fin n)) (hσ : σ • w = w) :
    (permutationAction (X ⊞ Y) n σ).asIso.hom ≫ binaryTensorWordProjection X Y n w =
      binaryTensorWordProjection X Y n w ≫ (binaryTensorWordFixedIso X Y n w σ hσ).hom := by
  apply binaryTensorWords_hom_ext X Y n
  intro z
  by_cases hz : z = w
  · subst z
    rw [← Category.assoc, ← binaryTensorWordFixedIso_inclusion, Category.assoc,
      binaryTensorWordInclusion_projection, Category.comp_id, ← Category.assoc,
      binaryTensorWordInclusion_projection, Category.id_comp]
  · have hn : σ • z ≠ w := by
      intro he
      have hh := congrArg (fun t => σ⁻¹ • t) (he.trans hσ.symm)
      exact hz (by simpa only [inv_smul_smul] using hh)
    rw [binaryTensorWordPermutation_component_ne X Y n σ z w hn, ← Category.assoc,
      binaryTensorWordInclusion_projection_ne X Y n z w hz, zero_comp]

/-- 元の和のテンソル冪に対する、指定された置換群を通した作用。 -/
def binaryTensorPowerAction {G : Type u} [Group G] (n : ℕ)
    (φ : G →* Equiv.Perm (Fin n)) : G →* End (power (X ⊞ Y) n) where
  toFun g := .of (permutationAction (X ⊞ Y) n (φ g)).asIso.hom
  map_one' := by apply End.ext; simp only [map_one]; rfl
  map_mul' g h := by apply End.ext; simp only [map_mul]; rfl

/-- 固定する群に関して、語の包含を表現の複体の射へ持ち上げる。 -/
def binaryTensorFixedRepresentationInclusion {G : Type u} [Group G]
    (n : ℕ) (w : BinaryTensorWord n) (φ : G →* Equiv.Perm (Fin n))
    (hφ : ∀ g, φ g • w = w) :
    binaryTensorWordFixedRepresentation X Y n w φ hφ ⟶
      representationCochainComplex (binaryTensorPowerAction X Y n φ) :=
  representationCochainMap _ _ (binaryTensorWordInclusion X Y n w)
    (fun g => binaryTensorWordFixedIso_inclusion X Y n w (φ g) (hφ g))

/-- 固定する群に関して、語の射影を表現の複体の射へ持ち上げる。 -/
def binaryTensorFixedRepresentationProjection {G : Type u} [Group G]
    (n : ℕ) (w : BinaryTensorWord n) (φ : G →* Equiv.Perm (Fin n))
    (hφ : ∀ g, φ g • w = w) :
    representationCochainComplex (binaryTensorPowerAction X Y n φ) ⟶
      binaryTensorWordFixedRepresentation X Y n w φ hφ :=
  representationCochainMap _ _ (binaryTensorWordProjection X Y n w)
    (fun g => binaryTensorWordFixedIso_projection X Y n w (φ g) (hφ g))

end SerrePositivity.EInfinity
end BinaryTensorMatrix
