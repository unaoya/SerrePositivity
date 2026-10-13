module

public import SerrePositivity.Spectra.SymmetricSequence.FreeBlockQuotient

/-! # 自由スペクトルの商表示の全単射の添字と対称群

標準のブロック直和を出力の有限集合へ移し、添字を対称群そのものと同一視する。
第一ブロックの前合成は右乗法、出力の後合成は左乗法となる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.SymmetricSequence

open CategoryTheory

/-- n≤mの場合の、標準のブロック直和と出力mとの同型。 -/
def freeBlockBaseIso (n m : ℕ) (hm : n ≤ m) :
    FiniteBijection.sumObj (FiniteBijection.of (m - n)) (FiniteBijection.of n) ≅
      FiniteBijection.of m :=
  eqToIso (congrArg FiniteBijection.of (Nat.sub_add_cancel hm))

/-- 標準のブロック直和の同型を使った、全単射の添字とΣ_mとの同値。 -/
def freePermutationIndex (n m : ℕ) (hm : n ≤ m) :
    FreeBlockIndex n m ≃ Equiv.Perm (Fin m) where
  toFun h := FiniteBijection.equivOfHom ((freeBlockBaseIso n m hm).inv ≫ h)
  invFun τ := (freeBlockBaseIso n m hm).hom ≫ FiniteBijection.permutation m τ
  left_inv h := by
    simp only [FiniteBijection.permutation, FiniteBijection.homOfEquiv_equivOfHom,
      Iso.hom_inv_id_assoc]
  right_inv τ := by
    simp only [Iso.inv_hom_id_assoc, FiniteBijection.permutation]
    exact FiniteBijection.equivOfHom_homOfEquiv
      (X := FiniteBijection.of m) (Y := FiniteBijection.of m) τ

/-- 添字に対応する置換の射は、標準同型の逆と添字の合成。 -/
lemma permutation_freePermutationIndex (n m : ℕ) (hm : n ≤ m) (h : FreeBlockIndex n m) :
    FiniteBijection.permutation m (freePermutationIndex n m hm h) =
      (freeBlockBaseIso n m hm).inv ≫ h :=
  FiniteBijection.homOfEquiv_equivOfHom _

/-- 第一ブロックの置換を出力mの置換へ移したもの。 -/
def freeBlockPermutation (n m : ℕ) (hm : n ≤ m) (σ : Equiv.Perm (Fin (m - n))) :
    Equiv.Perm (Fin m) :=
  FiniteBijection.equivOfHom ((freeBlockBaseIso n m hm).inv ≫
    FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫
      (freeBlockBaseIso n m hm).hom)

/-- 出力へ移した第一ブロックの置換の射の公式。 -/
lemma permutation_freeBlockPermutation (n m : ℕ) (hm : n ≤ m)
    (σ : Equiv.Perm (Fin (m - n))) :
    FiniteBijection.permutation m (freeBlockPermutation n m hm σ) =
      (freeBlockBaseIso n m hm).inv ≫
        FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫
          (freeBlockBaseIso n m hm).hom :=
  FiniteBijection.homOfEquiv_equivOfHom _

/-- 第一ブロックの前合成は、出力の対称群の右乗法に対応する。 -/
lemma freePermutationIndex_block (n m : ℕ) (hm : n ≤ m)
    (σ : Equiv.Perm (Fin (m - n))) (h : FreeBlockIndex n m) :
    freePermutationIndex n m hm
        (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h) =
      freePermutationIndex n m hm h * freeBlockPermutation n m hm σ := by
  apply (FiniteBijection.homEquiv (FiniteBijection.of m) (FiniteBijection.of m)).symm.injective
  change FiniteBijection.permutation m _ = FiniteBijection.permutation m _
  rw [FiniteBijection.permutation_mul, permutation_freePermutationIndex,
    permutation_freeBlockPermutation, permutation_freePermutationIndex]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 第一ブロックの恒等置換は出力の恒等置換へ送られる。 -/
@[simp] lemma freeBlockPermutation_one (n m : ℕ) (hm : n ≤ m) :
    freeBlockPermutation n m hm 1 = 1 := by
  apply (FiniteBijection.homEquiv (FiniteBijection.of m) (FiniteBijection.of m)).symm.injective
  change FiniteBijection.permutation m _ = FiniteBijection.permutation m _
  rw [permutation_freeBlockPermutation, FiniteBijection.permutation_one,
    FiniteBijection.sumMap_id, Category.id_comp, Iso.inv_hom_id,
    FiniteBijection.permutation_one]

/-- 第一ブロックの置換の出力への移送は群の積を保つ。 -/
lemma freeBlockPermutation_mul (n m : ℕ) (hm : n ≤ m)
    (σ τ : Equiv.Perm (Fin (m - n))) :
    freeBlockPermutation n m hm (σ * τ) =
      freeBlockPermutation n m hm σ * freeBlockPermutation n m hm τ := by
  have hb : FiniteBijection.sumMap (FiniteBijection.permutation (m - n) (σ * τ))
      (𝟙 (FiniteBijection.of n)) =
    FiniteBijection.sumMap (FiniteBijection.permutation (m - n) τ) (𝟙 _) ≫
      FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) := by
    rw [FiniteBijection.sumMap_comp, Category.id_comp, FiniteBijection.permutation_mul]
  apply (FiniteBijection.homEquiv (FiniteBijection.of m) (FiniteBijection.of m)).symm.injective
  change FiniteBijection.permutation m _ = FiniteBijection.permutation m _
  rw [FiniteBijection.permutation_mul, permutation_freeBlockPermutation,
    permutation_freeBlockPermutation, permutation_freeBlockPermutation, hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- 第一ブロックの対称群から出力の対称群への準同型。 -/
def freeBlockPermutationHom (n m : ℕ) (hm : n ≤ m) :
    Equiv.Perm (Fin (m - n)) →* Equiv.Perm (Fin m) where
  toFun := freeBlockPermutation n m hm
  map_one' := freeBlockPermutation_one n m hm
  map_mul' := freeBlockPermutation_mul n m hm

/-- 出力の後合成は、出力の対称群の左乗法に対応する。 -/
lemma freePermutationIndex_output (n m : ℕ) (hm : n ≤ m)
    (τ : Equiv.Perm (Fin m)) (h : FreeBlockIndex n m) :
    freePermutationIndex n m hm (h ≫ FiniteBijection.permutation m τ) =
      τ * freePermutationIndex n m hm h := by
  apply (FiniteBijection.homEquiv (FiniteBijection.of m) (FiniteBijection.of m)).symm.injective
  change FiniteBijection.permutation m _ = FiniteBijection.permutation m _
  rw [FiniteBijection.permutation_mul, permutation_freePermutationIndex,
    permutation_freePermutationIndex, Category.assoc]

end SerrePositivity.SymmetricSequence
