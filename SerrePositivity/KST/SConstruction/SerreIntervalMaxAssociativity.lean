module
public import SerrePositivity.KST.SConstruction.SerreIntervalTripleExt
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxVertexValues
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorReindex

/-! # 元の max connection の結合則
概要：元の鎖区間の三重 tensor 上で、max の二つの反復を厳密に比較する。
方針：元の生成元の三つ組で判定し、二つ以上の辺を含む総次数は零性で処理する。
規約：元の結合射と max chain map を保持する。使われ方：cubical connection の関係式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

private abbrev maxAssocAt (i j k : Fin 3) (p n : ℤ)
    (hp : serreIntervalGeneratorDegree i + serreIntervalGeneratorDegree j = p)
    (hn : p + serreIntervalGeneratorDegree k = n) : Prop :=
  let x := ιTensorObj (serreInterval A ⊗ serreInterval A) (serreInterval A)
    p (serreIntervalGeneratorDegree k) n hn
      (ιTensorObj (serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree i) (serreIntervalGeneratorDegree j) p hp
          (serreIntervalGenerator A i ⊗ₜ[A] serreIntervalGenerator A j) ⊗ₜ[A]
        serreIntervalGenerator A k)
  ((serreIntervalMax A ⊗ₘ 𝟙 (serreInterval A)) ≫ serreIntervalMax A).f n x =
    ((α_ (serreInterval A) (serreInterval A) (serreInterval A)).hom ≫
      (𝟙 (serreInterval A) ⊗ₘ serreIntervalMax A) ≫ serreIntervalMax A).f n x

private lemma max_assoc_000 :
    maxAssocAt A 0 0 0 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply]

private lemma max_assoc_001 :
    maxAssocAt A 0 0 1 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply]

private lemma max_assoc_002 :
    maxAssocAt A 0 0 2 (0) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (-1) (0) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply]

private lemma max_assoc_010 :
    maxAssocAt A 0 1 0 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_zero]

private lemma max_assoc_011 :
    maxAssocAt A 0 1 1 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_one]

private lemma max_assoc_012 :
    maxAssocAt A 0 1 2 (0) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (-1) (0) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_edge, TensorProduct.tmul_zero, map_zero]

private lemma max_assoc_020 :
    maxAssocAt A 0 2 0 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (-1) (0) (-1) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_edge_zero]

private lemma max_assoc_021 :
    maxAssocAt A 0 2 1 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (-1) (0) (-1) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_edge_one, TensorProduct.tmul_zero, map_zero]

private lemma max_assoc_022 :
    maxAssocAt A 0 2 2 (-1) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_100 :
    maxAssocAt A 1 0 0 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_zero]

private lemma max_assoc_101 :
    maxAssocAt A 1 0 1 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_zero, serreIntervalMax_one_one]

private lemma max_assoc_102 :
    maxAssocAt A 1 0 2 (0) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (-1) (0) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_one_zero, serreIntervalMax_one_edge]

private lemma max_assoc_110 :
    maxAssocAt A 1 1 0 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_zero,
    serreIntervalMax_one_one]

private lemma max_assoc_111 :
    maxAssocAt A 1 1 1 (0) (0) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (0) (0) (0) (0) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_one]

private lemma max_assoc_112 :
    maxAssocAt A 1 1 2 (0) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (0) (-1) (0) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_one,
    serreIntervalMax_one_edge, TensorProduct.tmul_zero, map_zero]

private lemma max_assoc_120 :
    maxAssocAt A 1 2 0 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (-1) (0) (-1) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_edge,
    serreIntervalMax_edge_zero, TensorProduct.zero_tmul, map_zero]

private lemma max_assoc_121 :
    maxAssocAt A 1 2 1 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (0) (-1) (0) (-1) (-1) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_edge,
    serreIntervalMax_edge_one, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

private lemma max_assoc_122 :
    maxAssocAt A 1 2 2 (-1) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_200 :
    maxAssocAt A 2 0 0 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (-1) (0) (0) (-1) (0) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_edge_zero]

private lemma max_assoc_201 :
    maxAssocAt A 2 0 1 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (-1) (0) (0) (-1) (0) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_zero_apply,
    serreIntervalMax_edge_zero, serreIntervalMax_edge_one]

private lemma max_assoc_202 :
    maxAssocAt A 2 0 2 (-1) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_210 :
    maxAssocAt A 2 1 0 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (-1) (0) (0) (-1) (0) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_zero,
    serreIntervalMax_edge_one, TensorProduct.zero_tmul, map_zero]

private lemma max_assoc_211 :
    maxAssocAt A 2 1 1 (-1) (-1) (by decide) (by decide) := by
  dsimp only [maxAssocAt, serreIntervalGeneratorDegree, serreIntervalGenerator]
  simp only [chain_comp_apply]
  rw [tensorMap_apply]
  erw [associator_apply_of_sums (serreInterval A) (serreInterval A) (serreInterval A)
    (-1) (0) (0) (-1) (0) (-1) (by decide) (by decide) (by decide)]
  rw [tensorMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply, serreIntervalMax_one_one,
    serreIntervalMax_edge_one, TensorProduct.zero_tmul, map_zero]

private lemma max_assoc_212 :
    maxAssocAt A 2 1 2 (-1) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_220 :
    maxAssocAt A 2 2 0 (-2) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_221 :
    maxAssocAt A 2 2 1 (-2) (-2) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-2))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-2) (by decide) (by decide))) _ _

private lemma max_assoc_222 :
    maxAssocAt A 2 2 2 (-2) (-3) (by decide) (by decide) := by
  exact @Subsingleton.elim ((serreInterval A).X (-3))
    (ModuleCat.subsingleton_of_isZero
      (serreInterval_isZero_X A (-3) (by decide) (by decide))) _ _

/-- 元の max connection は、元の三重 tensor の結合射に沿って結合的。 -/
lemma serreIntervalMax_assoc :
    (serreIntervalMax A ⊗ₘ 𝟙 (serreInterval A)) ≫ serreIntervalMax A =
      (α_ (serreInterval A) (serreInterval A) (serreInterval A)).hom ≫
        (𝟙 (serreInterval A) ⊗ₘ serreIntervalMax A) ≫ serreIntervalMax A := by
  apply serreIntervalTriple_hom_ext A
  intro i j k n hn
  change maxAssocAt A i j k _ n rfl hn
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    first
    | have hn' : n = 0 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -1 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -2 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    | have hn' : n = -3 := by simpa [serreIntervalGeneratorDegree] using hn.symm
    rcases hn' with rfl
  · exact max_assoc_000 A
  · exact max_assoc_001 A
  · exact max_assoc_002 A
  · exact max_assoc_010 A
  · exact max_assoc_011 A
  · exact max_assoc_012 A
  · exact max_assoc_020 A
  · exact max_assoc_021 A
  · exact max_assoc_022 A
  · exact max_assoc_100 A
  · exact max_assoc_101 A
  · exact max_assoc_102 A
  · exact max_assoc_110 A
  · exact max_assoc_111 A
  · exact max_assoc_112 A
  · exact max_assoc_120 A
  · exact max_assoc_121 A
  · exact max_assoc_122 A
  · exact max_assoc_200 A
  · exact max_assoc_201 A
  · exact max_assoc_202 A
  · exact max_assoc_210 A
  · exact max_assoc_211 A
  · exact max_assoc_212 A
  · exact max_assoc_220 A
  · exact max_assoc_221 A
  · exact max_assoc_222 A

end SerrePositivity.KST.SConstruction
