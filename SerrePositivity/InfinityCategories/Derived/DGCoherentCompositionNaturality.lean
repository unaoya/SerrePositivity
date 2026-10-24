module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentComparisonNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionPrism
/-!
概要：二入力の coherent 合成単体は dg 関手による係数写像に自然である。
方針：時刻の二値と最後の頂点で Hom を分け、単位と AW 合成の保存を使う。
規約：Small 仮定なしに両入力と全時刻を同時に写す。
使われ方：実 dg coherent 合成 prism の全パラメーター自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]
lemma dgCoherentCompositionObj_naturality (Q : DGFunctor A D E) (x y z : D) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    (dgStandardEnrichedFunctor Q).obj
      (coherentCompositionObj (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) y) (ForgetEnrichment.of (Complex A) z) t i) =
      coherentCompositionObj (ForgetEnrichment.of (Complex A) (Q.obj x))
        (ForgetEnrichment.of (Complex A) (Q.obj y))
        (ForgetEnrichment.of (Complex A) (Q.obj z)) t i := by
  induction i using Fin.lastCases with
  | last =>
    simp only [coherentCompositionObj, Fin.lastCases_last]
    rfl
  | cast i =>
    by_cases h : t i = 0 <;>
      simp only [coherentCompositionObj, Fin.lastCases_castSucc, h, ite_true, ite_false] <;> rfl
lemma dgCoherentPostcomp_of_normalized
    {C C' : Type v} [Category.{u} C] [Category.{u} C']
    [SimplicialCategory C] [SimplicialCategory C'] (F : EnrichedFunctor SSet C C')
    {K : SSet.{u}} {a b x y : C} {a' b' : C'}
    (H : K ⟶ SimplicialCategory.sHom a b) (H' : K ⟶ SimplicialCategory.sHom a' b')
    (ha : F.obj a = a') (hb : F.obj b = b')
    (hx : a = x) (hy : b = y) (hx' : a' = F.obj x) (hy' : b' = F.obj y)
    (h : (H ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hy)) ≫ F.map x y =
      H' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx' hy')) :
    H ≫ F.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) = H' := by
  cases hx
  cases hy
  cases hx'
  cases hy'
  simpa only [eqToHom_refl, Category.comp_id] using h
lemma dgCoherentCompositionSimplex_naturality (Q : DGFunctor A D E) {x y z : D} {n : ℕ}
    (σ : StandardSimplex A x y n) (τ : StandardSimplex A y z n)
    (t : Fin (n + 1) →o Fin 2) :
    (coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      (Z := ForgetEnrichment.of (Complex A) z) σ τ t).comp SSet (dgStandardEnrichedFunctor Q) =
    coherentCompositionSimplex (C := ClosedCategory A E)
      (X := ForgetEnrichment.of (Complex A) (Q.obj x))
      (Y := ForgetEnrichment.of (Complex A) (Q.obj y))
      (Z := ForgetEnrichment.of (Complex A) (Q.obj z))
      (dgStandardSimplexMap (Q.map x y) σ) (dgStandardSimplexMap (Q.map y z) τ) t := by
  apply EnrichedFunctor.ext SSet
    (fun i => dgCoherentCompositionObj_naturality Q x y z t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  dsimp only [EnrichedFunctor.comp, coherentCompositionSimplex]
  let X := ForgetEnrichment.of (Complex A) x
  let Y := ForgetEnrichment.of (Complex A) y
  let Z := ForgetEnrichment.of (Complex A) z
  let F := dgStandardEnrichedFunctor Q
  let σ' := dgStandardSimplexMap (Q.map x y) σ
  let τ' := dgStandardSimplexMap (Q.map y z) τ
  have hσ : SSet.yonedaEquiv.symm σ ≫ F.map X Y = SSet.yonedaEquiv.symm σ' :=
    SSet.yonedaEquiv_symm_comp (X := standardHomSpace (R := A) x y) σ
      (dgStandardHomMap (Q.map x y))
  have hτ : SSet.yonedaEquiv.symm τ ≫ F.map Y Z = SSet.yonedaEquiv.symm τ' :=
    SSet.yonedaEquiv_symm_comp (X := standardHomSpace (R := A) y z) τ
      (dgStandardHomMap (Q.map y z))
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply dgCoherentPostcomp_of_normalized F _ _
      (dgCoherentCompositionObj_naturality Q x y z t (Fin.last (n + 1)))
      (dgCoherentCompositionObj_naturality Q x y z t (Fin.last (n + 1)))
      (coherentCompositionObj_last X Y Z n t) (coherentCompositionObj_last X Y Z n t)
      (coherentCompositionObj_last (F.obj X) (F.obj Y) (F.obj Z) n t)
      (coherentCompositionObj_last (F.obj X) (F.obj Y) (F.obj Z) n t)
    rw [coherentCompositionHom_last_last, coherentCompositionHom_last_last]
    rw [Category.assoc, F.map_id]
    rfl
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change Fin.last (n + 1) ≤ j.castSucc at h
    exact ((not_le.mpr (Fin.castSucc_lt_last j)) h).elim
  case cast.last i =>
    by_cases hi : t i = 0
    · apply dgCoherentPostcomp_of_normalized F _ _
        (dgCoherentCompositionObj_naturality Q x y z t i.castSucc)
        (dgCoherentCompositionObj_naturality Q x y z t (Fin.last (n + 1)))
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_last X Y Z n t)
        (coherentCompositionObj_zero (F.obj X) (F.obj Y) (F.obj Z) t i hi)
        (coherentCompositionObj_last (F.obj X) (F.obj Y) (F.obj Z) n t)
      rw [coherentCompositionHom_zero_last (C := ClosedCategory A D)
          (X := X) (Y := Y) (Z := Z) σ τ t i hi,
        coherentCompositionHom_zero_last (C := ClosedCategory A E)
          (X := F.obj X) (Y := F.obj Y) (Z := F.obj Z) σ' τ' t i hi]
      rw [Category.assoc, F.map_comp]
      rw [← Category.assoc, CartesianMonoidalCategory.lift_map]
      simp only [Category.assoc]
      rw [hσ, hτ]
    · apply dgCoherentPostcomp_of_normalized F _ _
        (dgCoherentCompositionObj_naturality Q x y z t i.castSucc)
        (dgCoherentCompositionObj_naturality Q x y z t (Fin.last (n + 1)))
        (coherentCompositionObj_one X Y Z t i hi) (coherentCompositionObj_last X Y Z n t)
        (coherentCompositionObj_one (F.obj X) (F.obj Y) (F.obj Z) t i hi)
        (coherentCompositionObj_last (F.obj X) (F.obj Y) (F.obj Z) n t)
      rw [coherentCompositionHom_one_last (C := ClosedCategory A D)
          (X := X) (Y := Y) (Z := Z) σ τ t i hi,
        coherentCompositionHom_one_last (C := ClosedCategory A E)
          (X := F.obj X) (Y := F.obj Y) (Z := F.obj Z) σ' τ' t i hi]
      simp only [Category.assoc]
      rw [hτ]
  case cast.cast i j =>
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · apply dgCoherentPostcomp_of_normalized F _ _
        (dgCoherentCompositionObj_naturality Q x y z t i.castSucc)
        (dgCoherentCompositionObj_naturality Q x y z t j.castSucc)
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_zero X Y Z t j hj)
        (coherentCompositionObj_zero (F.obj X) (F.obj Y) (F.obj Z) t i hi)
        (coherentCompositionObj_zero (F.obj X) (F.obj Y) (F.obj Z) t j hj)
      rw [coherentCompositionHom_zero_zero (C := ClosedCategory A D)
          (X := X) (Y := Y) (Z := Z) σ τ t i j hi hj,
        coherentCompositionHom_zero_zero (C := ClosedCategory A E)
          (X := F.obj X) (Y := F.obj Y) (Z := F.obj Z) σ' τ' t i j hi hj]
      rw [Category.assoc, F.map_id]
    · apply dgCoherentPostcomp_of_normalized F _ _
        (dgCoherentCompositionObj_naturality Q x y z t i.castSucc)
        (dgCoherentCompositionObj_naturality Q x y z t j.castSucc)
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_one X Y Z t j hj)
        (coherentCompositionObj_zero (F.obj X) (F.obj Y) (F.obj Z) t i hi)
        (coherentCompositionObj_one (F.obj X) (F.obj Y) (F.obj Z) t j hj)
      rw [coherentCompositionHom_zero_one (C := ClosedCategory A D)
          (X := X) (Y := Y) (Z := Z) σ τ t i j hi hj,
        coherentCompositionHom_zero_one (C := ClosedCategory A E)
          (X := F.obj X) (Y := F.obj Y) (Z := F.obj Z) σ' τ' t i j hi hj]
      simp only [Category.assoc]
      rw [hσ]
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact (pathCut_backward_false t hi hj (P.obj 0)).elim
    · apply dgCoherentPostcomp_of_normalized F _ _
        (dgCoherentCompositionObj_naturality Q x y z t i.castSucc)
        (dgCoherentCompositionObj_naturality Q x y z t j.castSucc)
        (coherentCompositionObj_one X Y Z t i hi) (coherentCompositionObj_one X Y Z t j hj)
        (coherentCompositionObj_one (F.obj X) (F.obj Y) (F.obj Z) t i hi)
        (coherentCompositionObj_one (F.obj X) (F.obj Y) (F.obj Z) t j hj)
      rw [coherentCompositionHom_one_one (C := ClosedCategory A D)
          (X := X) (Y := Y) (Z := Z) σ τ t i j hi hj,
        coherentCompositionHom_one_one (C := ClosedCategory A E)
          (X := F.obj X) (Y := F.obj Y) (Z := F.obj Z) σ' τ' t i j hi hj]
      rw [Category.assoc, F.map_id]
end SerrePositivity.InfinityCategories
