module
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.KST.SConstruction.DGFunctorHomElements
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：最終 cell 分解内の初期 cycle 生成元と、native Hom が満たす厳密な自然性。
方針：初期 sphereLift を段零の包含で送り、comparison の余極限等式を用いる。
規約：増大後の自然性で代用しない。全 native Hom 作用の存在は未主張。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded HomologicalComplex KST.SConstruction
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 初期被覆の全 cycle 生成元を、同じ最終分解内へ送る sphere 射。 -/
def dgCellCycleSphere (x y : C) (n : ℤ)
    (z : complexCycles R (homObject R C x y) n) :
    complexSphere R n ⟶ homObject R (Source R C) ⟨x⟩ ⟨y⟩ :=
  DGCategoryCycleCover.sphereLift R C x y n z ≫ stageInclusion R C 0 x y

/-- 増大後には、指定した元の cycle を厳密に回収する。 -/
lemma dgCellCycleSphere_augmentation (x y : C) (n : ℤ)
    (z : complexCycles R (homObject R C x y) n) :
    dgCellCycleSphere R C x y n z ≫ (augmentation R C).map ⟨x⟩ ⟨y⟩ =
      complexSphereMap R n z := by
  rw [dgCellCycleSphere, Category.assoc]
  change DGCategoryCycleCover.sphereLift R C x y n z ≫
    (stageInclusion R C 0 x y ≫ candidateAugmentation R C x y) = _
  rw [stageInclusion_augmentation]
  exact DGCategoryCycleCover.sphereLift_augmentation R C x y n z

variable (D : Type v) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)

/-- 比較関手は、元の cycle の像を添字とする同じ初期生成元へ送る。 -/
lemma dgCellCycleSphere_comparison (x y : C) (n : ℤ)
    (z : complexCycles R (homObject R C x y) n) :
    dgCellCycleSphere R C x y n z ≫
        (comparisonFunctor R C D F).map ⟨x⟩ ⟨y⟩ =
      dgCellCycleSphere R D (F.obj x) (F.obj y) n
        (complexMapCycle R (F.map x y) n z) := by
  unfold dgCellCycleSphere
  change DGCategoryCycleCover.sphereLift R C x y n z ≫
    stageInclusion R C 0 x y ≫ comparisonHom R C D F x y = _
  rw [stageInclusion_comparison]
  change DGCategoryCycleCover.sphereLift R C x y n z ≫
    (DGCategoryCycleCover.map R C D F).map x y ≫ _ = _
  have hs : DGCategoryCycleCover.sphereLift R C x y n z ≫
      (DGCategoryCycleCover.map R C D F).map x y =
      DGCategoryCycleCover.sphereLift R D (F.obj x) (F.obj y) n
        (complexMapCycle R (F.map x y) n z) := by
    unfold DGCategoryCycleCover.sphereLift
    rw [Category.assoc, DGCategoryCycleCover.edge_map,
      ← Category.assoc, complexCycleCoverLift_map]
  rw [← Category.assoc, hs]

/-- 同じ比較等式を斉次生成元の値として回収する。 -/
lemma dgCellCycleSphere_comparison_element (x y : C) (n : ℤ)
    (z : complexCycles R (homObject R C x y) n) :
    ((comparisonFunctor R C D F).map ⟨x⟩ ⟨y⟩).f n
        (complexSphereCycle R n (dgCellCycleSphere R C x y n z)).val =
      (complexSphereCycle R n (dgCellCycleSphere R D (F.obj x) (F.obj y) n
        (complexMapCycle R (F.map x y) n z))).val := by
  rw [← complexSphereCycle_comp, dgCellCycleSphere_comparison]

/-- native 関手圏の斉次元は、分解内の初期生成元についても厳密な自然性を満たす。 -/
lemma dgCellComparisonHom_initialNaturality (G : DGFunctor R C D) {q p n : ℤ}
    (t : (dgFunctorHom R (Source R C) (Source R D)
      (comparisonFunctor R C D F) (comparisonFunctor R C D G)).X q)
    (x y : C) (z : complexCycles R (homObject R C x y) p) (hn : q + p = n) :
    (q * p).negOnePow • forward R
      ((comparisonFunctor R C D F).map ⟨x⟩ ⟨y⟩ |>.f p
        (complexSphereCycle R p (dgCellCycleSphere R C x y p z)).val)
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨y⟩).f q t) (by omega) =
    forward R
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨x⟩).f q t)
      ((comparisonFunctor R C D G).map ⟨x⟩ ⟨y⟩ |>.f p
        (complexSphereCycle R p (dgCellCycleSphere R C x y p z)).val) hn :=
  dgFunctorHomElement_naturality R (Source R C) (Source R D) t
    (complexSphereCycle R p (dgCellCycleSphere R C x y p z)).val hn

/-- 初期生成元を両端で明示した、全次数 native Hom の必要条件。 -/
lemma dgCellComparisonHom_initialNaturality_mapped (G : DGFunctor R C D) {q p n : ℤ}
    (t : (dgFunctorHom R (Source R C) (Source R D)
      (comparisonFunctor R C D F) (comparisonFunctor R C D G)).X q)
    (x y : C) (z : complexCycles R (homObject R C x y) p) (hn : q + p = n) :
    (q * p).negOnePow • forward R
      (complexSphereCycle R p (dgCellCycleSphere R D (F.obj x) (F.obj y) p
        (complexMapCycle R (F.map x y) p z))).val
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨y⟩).f q t) (by omega) =
    forward R
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨x⟩).f q t)
      (complexSphereCycle R p (dgCellCycleSphere R D (G.obj x) (G.obj y) p
        (complexMapCycle R (G.map x y) p z))).val hn := by
  have h := dgCellComparisonHom_initialNaturality R C D F G t x y z hn
  rwa [dgCellCycleSphere_comparison_element, dgCellCycleSphere_comparison_element] at h

/-- 元の単位をラベルとする初期生成元。分解圏の圏論的単位とは区別する。 -/
def dgCellUnitCycle (x : C) : zeroCycles (homObject R (Source R C) ⟨x⟩ ⟨x⟩) :=
  complexSphereCycle R 0 (dgCellCycleSphere R C x x 0 (unitElement R x))

/-- 入力の自然性では自明な単位も、cell 分解では生成元として自然性を要求する。 -/
lemma dgCellComparisonHom_unitGeneratorNaturality (G : DGFunctor R C D) {q : ℤ}
    (t : (dgFunctorHom R (Source R C) (Source R D)
      (comparisonFunctor R C D F) (comparisonFunctor R C D G)).X q) (x : C) :
    forward R (p := 0) (q := q) (n := q) (dgCellUnitCycle R D (F.obj x)).val
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨x⟩).f q t) (by omega) =
    forward R (p := q) (q := 0) (n := q)
      ((dgFunctorHomπ R _ _ (comparisonFunctor R C D F)
        (comparisonFunctor R C D G) ⟨x⟩).f q t)
      (dgCellUnitCycle R D (G.obj x)).val (by omega) := by
  have h := dgCellComparisonHom_initialNaturality_mapped R C D F G t x x
    (unitElement R x) (n := q) (by omega)
  have hf : complexMapCycle R (F.map x x) 0 (unitElement R x) =
      unitElement R (F.obj x) := Subtype.ext (F.map_unitElement R x)
  have hg : complexMapCycle R (G.map x x) 0 (unitElement R x) =
      unitElement R (G.obj x) := Subtype.ext (G.map_unitElement R x)
  simpa only [hf, hg, mul_zero, Int.negOnePow_zero, one_smul, dgCellUnitCycle] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
