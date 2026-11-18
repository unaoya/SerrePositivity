module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.StandardQuotientCompatibility

/-!
# 標準語から自由 Schur 比較への接続

HA 3.2.4.7 の自由比較で、指定標準語の包含を軌道直和へ接続する。
BS-W16 の型一覧 L06〜L08。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local instance] Classical.propDecidable
variable (R : Type u) [CommRing R] (X Y : Complex R)

/-- 指定標準語の arity 商は、同じ標準軌道の指定包含となる。 -/
lemma schurArityOrbitIso_standard_quotient (m n : ℕ) :
    ((operad R).arity (m + n) ◁ ((binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n))) ≫
    arityCoinvariantComplexQuotient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram R (sequence R) (X ⊞ Y)) (m + n) ≫
      (schurArityOrbitIso X Y (m + n)).hom =
    (β_ ((operad R).arity (m + n)) (power X m ⊗ power Y n)).hom ≫
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (twoColorSourceComplexAction R m n) ≫
    (orbitStandardCoefficientIso X Y m n).inv ≫
      Sigma.ι (orbitCoefficientComplex X Y (m + n)) (ULift.up ⟨m, by omega⟩) := by
  let e := eqToIso (congrArg (binaryTensorWordObj X Y (m + n))
    (binaryTensorCountPattern_add m n)) ≪≫ binaryTensorStandardPowersIso X Y m n
  apply (cancel_epi ((operad R).arity (m + n) ◁ e.hom)).1
  have he : e.hom ≫ (binaryTensorStandardPowersIso X Y m n).inv ≫
      binaryTensorWordInclusion X Y (m + n) (binaryTensorStandardPattern m n) =
      binaryTensorWordInclusion X Y (m + n) (binaryTensorCountPattern (m + n) ⟨m, by omega⟩) := by
    simp only [e, Iso.trans_hom, eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc]
    exact binaryTensorWordInclusion_word_eq X Y (binaryTensorCountPattern_add m n)
  rw [← whiskerLeft_comp_assoc, he, schurArityOrbitIso_word_quotient]
  have hb := BraidedCategory.braiding_naturality (𝟙 ((operad R).arity (m + n))) e.hom
  simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id,
    Category.id_comp, Category.comp_id] at hb
  rw [reassoc_of% hb]
  erw [← reassoc_of% (orbitStandardCoefficientIso_quotient R X Y m n)]
  simp only [Iso.hom_inv_id_assoc]

set_option maxHeartbeats 800000 in
-- 再添字付けの定義を含む同じ直和の型照合に限定した上限。
/-- 全 arity の再添字付けも、同じ標準軌道の指定包含を保つ。 -/
lemma freeStandardSource_binaryOrbit (m n : ℕ) :
    freeStandardSource R X Y m n ≫ (schurBinaryOrbitIso X Y).hom =
    (β_ ((operad R).arity (m + n)) (power X m ⊗ power Y n)).hom ≫
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (twoColorSourceComplexAction R m n) ≫
    (orbitStandardCoefficientIso X Y m n).inv ≫
      Sigma.ι (fun p : ℕ × ℕ => orbitCoefficientComplex X Y (p.1 + p.2)
        (ULift.up ⟨p.1, by omega⟩)) (m, n) := by
  simp only [freeStandardSource, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι, schurBinaryOrbitIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, schurComplexArityIso]
  rw [reassoc_of% (arityCoinvariantComplexIso_ι
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram R (sequence R) (X ⊞ Y)) (m + n)), Sigma.ι_mapIso_hom_assoc]
  rw [reassoc_of% (schurArityOrbitIso_standard_quotient R X Y m n)]
  simp only [sigmaSigmaIso_hom, Sigma.ι_comp_desc_assoc]
  erw [Sigma.ι_reindex_inv binaryTensorCountIndexEquiv.symm
    (fun p => orbitCoefficientComplex X Y p.1 p.2) (m, n)]
  rfl

/-- 元の指定標準語上で、係数比較の同値の順射は指定係数射そのもの。 -/
lemma freeStandardSource_coefficientComparison (m n : ℕ) :
    freeStandardSource R X Y m n ≫ (freeSchurCoefficientHomotopyEquiv X Y).hom =
      freeStandardTarget R X Y m n := by
  apply (cancel_mono (schurTensorArityIso X Y).hom).1
  simp only [freeSchurCoefficientHomotopyEquiv, HomotopyEquiv.trans_hom,
    HomotopyEquiv.ofIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (freeStandardSource_binaryOrbit R X Y m n)]
  simp only [complexCoproductHomotopyEquiv, Sigma.ι_map, Category.assoc,
    orbitCoefficientComparisonEquiv, HomotopyEquiv.trans_hom, HomotopyEquiv.ofIso,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% (twoColorCoefficientTarget_schurQuotient R X Y m n)]
  simp only [freeStandardTarget, Category.assoc, schurTensorArityIso_generators]

end SerrePositivity.EInfinity.BarrattEccles
