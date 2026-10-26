module
public import SerrePositivity.InfinityCategories.Derived.DGStandardHomChainMap
public import SerrePositivity.InfinityCategories.Derived.MooreCyclesNaturality
/-!
概要：Hom 鎖写像と標準 Moore 正規化の全成分比較との自然性を計算する。
方針：正規化部分対象の包含で実単体を回収し、最上位成分で検査する。
規約：既存の正規化同型と元の Hom 鎖写像を保持する。
使われ方：実 pinched 評価の Moore ホモロジーを元の評価コホモロジーへ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology DifferentialGraded DoldKanComparison
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

/-- 標準座標上の全単体的加群射。 -/
def dgBarCompactStandardModuleMap (φ : homObject R D x y ⟶ homObject R E a b) :
    standardModule (R := R) x y ⟶ standardModule (R := R) a b where
  app n := ModuleCat.ofHom
    (((standardSimplexEquiv a b n.unop.len).toLinearMap.comp (pinchedLinearSimplexMap φ)).comp
      (standardSimplexEquiv x y n.unop.len).symm.toLinearMap)
  naturality {m n} α := by
    ext s
    exact dgStandardSimplexMap_pullback φ α.unop.toOrderHom s

lemma dgBarCompactStandardModuleMap_apply
    (φ : homObject R D x y ⟶ homObject R E a b) (n : SimplexCategoryᵒᵖ)
    (s : (standardModule (R := R) x y).obj n) :
    (dgBarCompactStandardModuleMap φ).app n s = dgStandardSimplexMap φ s := rfl

lemma dgBarCompactStandardMooreTermIso_map_val
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ)
    (s : ((normalizedMooreComplex (ModuleCat.{u} R)).obj
      (standardModule (R := R) x y)).X n) :
    (((standardMooreTermIso a b n).hom
      (((normalizedMooreComplex (ModuleCat.{u} R)).map
        (dgBarCompactStandardModuleMap φ)).f n s))).val =
      dgStandardSimplexMap φ (((standardMooreTermIso x y n).hom s).val) := by
  have h := ConcreteCategory.congr_hom
    (normalizedMooreMap_arrow (dgBarCompactStandardModuleMap φ) n) s
  rw [← standardMooreTermIso_hom_subtype, ← standardMooreTermIso_hom_subtype] at h
  exact h

lemma dgBarCompactStandardMoorePositiveIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{u} R)).map
      (dgBarCompactStandardModuleMap φ)).f (n + 1) ≫
        (standardMoorePositiveIso a b n).hom =
      (standardMoorePositiveIso x y n).hom ≫ φ.f (-(n + 1 : ℤ)) := by
  ext s
  change (((standardMooreTermIso a b (n + 1)).hom
    (((normalizedMooreComplex (ModuleCat.{u} R)).map
      (dgBarCompactStandardModuleMap φ)).f (n + 1) s)).val.val.component
        Finset.univ (-(n + 1 : ℤ)) Finset.univ_nonempty (by simp)) = _
  rw [dgBarCompactStandardMooreTermIso_map_val, dgStandardSimplexMap_component]
  rfl

lemma dgBarCompactStandardMooreZeroIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) :
    ((normalizedMooreComplex (ModuleCat.{u} R)).map
      (dgBarCompactStandardModuleMap φ)).f 0 ≫
        (standardMooreZeroIso a b).hom ≫ (connectiveHomComplex_zeroIso a b).hom ≫
          (homObject R E a b).iCycles 0 =
      (standardMooreZeroIso x y).hom ≫ (connectiveHomComplex_zeroIso x y).hom ≫
        (homObject R D x y).iCycles 0 ≫ φ.f 0 := by
  rw [← connectiveHomComplex_zeroCyclesIso_hom_subtype a b]
  conv_rhs =>
    rw [← Category.assoc (connectiveHomComplex_zeroIso x y).hom
      ((homObject R D x y).iCycles 0) (φ.f 0),
      ← connectiveHomComplex_zeroCyclesIso_hom_subtype x y]
  simp only [standardMooreZeroIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  ext s
  change (((standardMooreTermIso a b 0).hom
    (((normalizedMooreComplex (ModuleCat.{u} R)).map
      (dgBarCompactStandardModuleMap φ)).f 0 s)).val.val.component
        Finset.univ 0 Finset.univ_nonempty (by simp)) = _
  rw [dgBarCompactStandardMooreTermIso_map_val, dgStandardSimplexMap_component]
  rfl

/-- 標準正規化は、元の Hom 鎖写像の smart truncation と可換する。 -/
lemma dgBarCompactStandardNormalizationIso_naturality
    (φ : homObject R D x y ⟶ homObject R E a b) :
    (normalizedMooreComplex (ModuleCat.{u} R)).map
        (dgBarCompactStandardModuleMap φ) ≫ (standardNormalizationIso a b).hom =
      (standardNormalizationIso x y).hom ≫
        HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    apply (cancel_mono ((connectiveHomComplex_zeroIso a b).hom ≫
      (homObject R E a b).iCycles 0)).mp
    change (_ ≫ (standardMooreZeroIso a b).hom) ≫ _ =
      ((standardMooreZeroIso x y).hom ≫
        (HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)).f 0) ≫ _
    rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap (i' := (0 : ℤ)) φ _
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl) (by simp)]
    simp only [connectiveHomComplex_zeroIso, Category.assoc, Iso.inv_hom_id_assoc]
    rw [HomologicalComplex.cyclesMap_i]
    exact dgBarCompactStandardMooreZeroIso_naturality φ
  | succ n =>
    apply (cancel_mono (connectiveHomComplex_positiveIso a b n).hom).mp
    change (_ ≫ ((standardMoorePositiveIso a b n).hom ≫
      (connectiveHomComplex_positiveIso a b n).inv)) ≫ _ =
      (((standardMoorePositiveIso x y n).hom ≫
        (connectiveHomComplex_positiveIso x y n).inv) ≫
          (HomologicalComplex.truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)).f (n+1)) ≫ _
    rw [HomologicalComplex.truncLE'Map_f_eq (i' := -(n + 1 : ℤ)) φ _
      (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; omega) (by simp)]
    simpa only [connectiveHomComplex_positiveIso, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
        dgBarCompactStandardMoorePositiveIso_naturality φ n

end SerrePositivity.InfinityCategories
