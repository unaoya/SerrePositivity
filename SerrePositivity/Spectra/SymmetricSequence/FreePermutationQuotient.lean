module

public import SerrePositivity.Spectra.SymmetricSequence.FreePermutationIndex
public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotientMaps

/-! # 対称群そのもので添字付けた自由convolutionの商表示

Σ_mで添字付けた余積を、第一ブロックの対称群の右乗法とテンソル積への作用の関係式で割る。
全単射で添字付けた既存の商と、生成元上で互いに逆となる比較を構成する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 出力の対称群Σ_mで添字付けた生成元の余積。 -/
def freePermutationGenerators (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) : C :=
  ∐ (fun _ : Equiv.Perm (Fin m) => F.obj (FiniteBijection.of (m - n)) ⊗ X)

/-- 第一ブロックの対称群と出力の対称群で添字付けた関係式の余積。 -/
def freePermutationRelations (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) : C :=
  ∐ (fun _ : Equiv.Perm (Fin (m - n)) × Equiv.Perm (Fin m) =>
    F.obj (FiniteBijection.of (m - n)) ⊗ X)

/-- 関係式の左辺は第一ブロックの置換をテンソル積へ作用させる。 -/
def freePermutationRelationLeft (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freePermutationRelations F n X m ⟶ freePermutationGenerators F n X m :=
  Sigma.desc (fun r => F.map (FiniteBijection.permutation (m - n) r.1) ▷ X ≫
    Sigma.ι (fun _ : Equiv.Perm (Fin m) => F.obj (FiniteBijection.of (m - n)) ⊗ X) r.2)

/-- 関係式の右辺は出力の置換へ第一ブロックの置換を右から掛ける。 -/
def freePermutationRelationRight (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : freePermutationRelations F n X m ⟶ freePermutationGenerators F n X m :=
  Sigma.desc (fun r =>
    Sigma.ι (fun _ : Equiv.Perm (Fin m) => F.obj (FiniteBijection.of (m - n)) ⊗ X)
      (r.2 * freeBlockPermutation n m hm r.1))

/-- Σ_mの余積を第一ブロックの対称群の関係式で割った誘導商。 -/
def freePermutationQuotient (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : C :=
  coequalizer (freePermutationRelationLeft F n X m) (freePermutationRelationRight F n X m hm)

/-- 出力の置換τに対応する誘導商の生成元。 -/
def freePermutationQuotientGenerator (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) (τ : Equiv.Perm (Fin m)) : F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶
      freePermutationQuotient F n X m hm :=
  Sigma.ι (fun _ : Equiv.Perm (Fin m) => F.obj (FiniteBijection.of (m - n)) ⊗ X) τ ≫
    coequalizer.π (freePermutationRelationLeft F n X m) (freePermutationRelationRight F n X m hm)

/-- 対称群の誘導商の生成元の関係式。 -/
@[reassoc] lemma freePermutationQuotientGenerator_relation (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m)
    (σ : Equiv.Perm (Fin (m - n))) (τ : Equiv.Perm (Fin m)) :
    F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫
        freePermutationQuotientGenerator F n X m hm τ =
      freePermutationQuotientGenerator F n X m hm (τ * freeBlockPermutation n m hm σ) := by
  have hc := congrArg (fun t =>
    Sigma.ι (fun _ : Equiv.Perm (Fin (m - n)) × Equiv.Perm (Fin m) =>
      F.obj (FiniteBijection.of (m - n)) ⊗ X) (σ, τ) ≫ t)
    (coequalizer.condition (freePermutationRelationLeft F n X m)
      (freePermutationRelationRight F n X m hm))
  simpa only [freePermutationQuotientGenerator, freePermutationRelationLeft,
    freePermutationRelationRight, Sigma.ι_comp_desc_assoc, Category.assoc] using hc

/-- 誘導商からの射は置換で添字付けた生成元上の値で決まる。 -/
lemma freePermutationQuotient_hom_ext (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) {Y : C} (f g : freePermutationQuotient F n X m hm ⟶ Y)
    (h : ∀ τ, freePermutationQuotientGenerator F n X m hm τ ≫ f =
      freePermutationQuotientGenerator F n X m hm τ ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro τ
  simpa only [freePermutationQuotientGenerator, Category.assoc] using h τ

/-- 誘導商の関係式を満たす生成元上の射の族からの降下。 -/
def freePermutationQuotientDesc (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) {Y : C}
    (t : Equiv.Perm (Fin m) → (F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶ Y))
    (ht : ∀ σ τ, F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫ t τ =
      t (τ * freeBlockPermutation n m hm σ)) : freePermutationQuotient F n X m hm ⟶ Y :=
  coequalizer.desc (Sigma.desc t) (by
    apply Sigma.hom_ext
    intro r
    simp only [freePermutationRelationLeft, freePermutationRelationRight,
      Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
    exact ht r.1 r.2)

/-- 降下した射は各置換の生成元上で指定された値に一致する。 -/
@[reassoc (attr := simp)] lemma freePermutationQuotientGenerator_desc
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m) {Y : C}
    (t : Equiv.Perm (Fin m) → (F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶ Y))
    (ht : ∀ σ τ, F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫ t τ =
      t (τ * freeBlockPermutation n m hm σ)) (τ : Equiv.Perm (Fin m)) :
    freePermutationQuotientGenerator F n X m hm τ ≫
      freePermutationQuotientDesc F n X m hm t ht = t τ := by
  simp only [freePermutationQuotientGenerator, freePermutationQuotientDesc,
    Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

/-- 全単射の商から、Σ_mで添字付けた商への射。 -/
def freeBlockToPermutationQuotient (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : freeBlockQuotient F n X m ⟶ freePermutationQuotient F n X m hm :=
  freeBlockQuotientDesc F n X m
    (fun h => freePermutationQuotientGenerator F n X m hm (freePermutationIndex n m hm h))
    (fun σ h => by
      rw [freePermutationQuotientGenerator_relation, freePermutationIndex_block])

/-- 全単射の商の生成元は、対応する置換の生成元へ送られる。 -/
@[reassoc (attr := simp)] lemma freeBlockToPermutationQuotient_generator
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m) (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ freeBlockToPermutationQuotient F n X m hm =
      freePermutationQuotientGenerator F n X m hm (freePermutationIndex n m hm h) :=
  freeBlockQuotientGenerator_desc F n X m _ _ h

/-- Σ_mで添字付けた商から、全単射の商への射。 -/
def freePermutationToBlockQuotient (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : freePermutationQuotient F n X m hm ⟶ freeBlockQuotient F n X m :=
  freePermutationQuotientDesc F n X m hm
    (fun τ => freeBlockQuotientGenerator F n X m ((freePermutationIndex n m hm).symm τ))
    (fun σ τ => by
      rw [freeBlockQuotientGenerator_relation]
      apply congrArg (freeBlockQuotientGenerator F n X m)
      apply (freePermutationIndex n m hm).injective
      rw [freePermutationIndex_block, Equiv.apply_symm_apply, Equiv.apply_symm_apply])

/-- 置換の生成元は、対応する全単射の生成元へ戻される。 -/
@[reassoc (attr := simp)] lemma freePermutationToBlockQuotient_generator
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (hm : n ≤ m)
    (τ : Equiv.Perm (Fin m)) :
    freePermutationQuotientGenerator F n X m hm τ ≫ freePermutationToBlockQuotient F n X m hm =
      freeBlockQuotientGenerator F n X m ((freePermutationIndex n m hm).symm τ) :=
  freePermutationQuotientGenerator_desc F n X m hm _ _ τ

/-- 全単射の商と、対称群そのもので添字付けた誘導商との比較同型。 -/
def freeBlockQuotientIsoPermutation (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (hm : n ≤ m) : freeBlockQuotient F n X m ≅ freePermutationQuotient F n X m hm where
  hom := freeBlockToPermutationQuotient F n X m hm
  inv := freePermutationToBlockQuotient F n X m hm
  hom_inv_id := by
    apply freeBlockQuotient_hom_ext
    intro h
    simp only [freeBlockToPermutationQuotient_generator_assoc,
      freePermutationToBlockQuotient_generator, Equiv.symm_apply_apply, Category.comp_id]
  inv_hom_id := by
    apply freePermutationQuotient_hom_ext
    intro τ
    simp only [freePermutationToBlockQuotient_generator_assoc,
      freeBlockToPermutationQuotient_generator, Equiv.apply_symm_apply, Category.comp_id]

end SerrePositivity.SymmetricSequence
