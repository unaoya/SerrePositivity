module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection

/-! # 定数複体塔の標準射による再構成

恒等遷移の差分は全射であることを証明し、Milnor列から標準射の準同型同値を得る。
任意の逆系のlim¹消滅は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 同一の複体を各段に置く定数塔。 -/
abbrev constantComplexTower (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ℕ → CochainComplex (ModuleCat.{u} R) ℤ := fun _ ↦ K

/-- 恒等遷移の定数塔への標準の対角射。 -/
def constantComplexTowerUnit (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ complexTowerHomotopyLimit R (constantComplexTower R K) (fun _ ↦ 𝟙 K) :=
  complexTowerCompatibleLift R _ _ K (fun _ ↦ 𝟙 K) (by intro n; simp)

/-- 対角射は全ての段への射影に対して恒等となる。 -/
theorem constantComplexTowerUnit_comp_projection (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℕ) :
    constantComplexTowerUnit R K ≫
      complexTowerProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) ≫
        Pi.π (constantComplexTower R K) n = 𝟙 K := by
  rw [← Category.assoc, constantComplexTowerUnit,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- 恒等遷移の定数塔では、ホモロジー上の差分は全射。 -/
theorem constantComplexTowerHomologyDifference_surjective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Surjective
      (complexTowerHomologyDifference R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i) := by
  apply moduleTowerDifference_surjective
  intro n y
  refine ⟨y, ?_⟩
  simp only [homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- Milnor列の符号規約では、対角射の境界像は定数列-xとなる。 -/
theorem constantComplexTowerUnit_boundary (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : ℤ) (x : K.homology i) (n : ℕ) :
    complexTowerHomologyBoundary R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (homologyMap (constantComplexTowerUnit R K) i x) n = -x := by
  rw [complexTowerHomologyBoundary_eq_neg_projection]
  simp only [Pi.neg_apply, complexProductHomologyEquiv_apply]
  have h := congrArg (fun f ↦ homologyMap f i)
    (constantComplexTowerUnit_comp_projection R K n)
  simpa only [homologyMap_comp, homologyMap_id, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
    congrArg (fun f ↦ -(f.hom x)) h

/-- 対角射は全次数のホモロジーで全単射。 -/
theorem constantComplexTowerUnit_homology_bijective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Function.Bijective (homologyMap (constantComplexTowerUnit R K) i) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z ↦ complexTowerHomologyBoundary R
      (constantComplexTower R K) (fun _ ↦ 𝟙 K) i z 0) h
    simpa only [constantComplexTowerUnit_boundary, neg_inj] using h'
  · intro y
    let z := complexTowerMilnorProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i y
    have hz (n : ℕ) : z.val n = z.val 0 := by
      induction n with
      | zero => rfl
      | succ n ih =>
        have h := (mem_moduleTowerLimit_iff R _ _ z.val).mp z.property n
        simpa only [homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] using h.trans ih
    refine ⟨-(z.val 0), ?_⟩
    apply complexTowerMilnorProjection_injective_of_surjective R
      (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (constantComplexTowerHomologyDifference_surjective R K (i - 1))
    apply Subtype.ext
    funext n
    change complexTowerHomologyBoundary R (constantComplexTower R K) (fun _ ↦ 𝟙 K) i
      (homologyMap (constantComplexTowerUnit R K) i (-(z.val 0))) n = z.val n
    rw [constantComplexTowerUnit_boundary, neg_neg]
    exact (hz n).symm

/-- 任意複体から恒等遷移の定数塔のholimへの標準射は準同型同値。 -/
theorem constantComplexTowerUnit_quasiIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (constantComplexTowerUnit R K) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact constantComplexTowerUnit_homology_bijective R K i

/-- 実導来圏で、定数塔のholimは標準射を通じて元の対象と同型。 -/
def constantComplexTowerUnitIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj K ≅
      complexTowerHomotopyLimitObject R (constantComplexTower R K) (fun _ ↦ 𝟙 K) := by
  have := constantComplexTowerUnit_quasiIso R K
  exact asIso (DerivedCategory.Q.map (constantComplexTowerUnit R K))

/-- 再構成同型の逆射は、定数塔の第0段への標準射影。 -/
theorem constantComplexTowerUnitIso_inv (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (constantComplexTowerUnitIso R K).inv =
      DerivedCategory.Q.map
        (complexTowerProjection R (constantComplexTower R K) (fun _ ↦ 𝟙 K) ≫
          Pi.π (constantComplexTower R K) 0) := by
  apply (cancel_epi (constantComplexTowerUnitIso R K).hom).mp
  rw [Iso.hom_inv_id]
  change 𝟙 _ = DerivedCategory.Q.map (constantComplexTowerUnit R K) ≫ _
  rw [← CategoryTheory.Functor.map_comp, constantComplexTowerUnit_comp_projection,
    CategoryTheory.Functor.map_id]

end SerrePositivity.DerivedCompletion
