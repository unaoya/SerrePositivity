module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCech
public import SerrePositivity.AlgebraicGeometry.CechTupleReindex

/-!
概要：整数鎖を、任意の小さい開集合上で Čech コチェインに評価する。
方針：各タプルの切断を制限し、整数係数の有限和を取る。
規約：指定した開集合が交叉に含まれない成分は零で評価する。
使われ方：細分の選択の比較ホモトピーを切断のコチェインへ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
open scoped BigOperators Classical
universe u v w
variable {X : Type u} [TopologicalSpace X] {R : Type w} [CommRing R]
variable {ι : Type} [DecidableEq ι]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X)

/-- タプルの整数鎖を、指定した開集合上の切断として評価する。 -/
def openCoverCechEvaluateAt (W : Opens X) (k : ℕ) :
    CechTupleChains ι k →ₗ[ℤ]
      (FullCechCochains (openCoverCechDiagram P U) k →ₗ[R] P.obj (Opposite.op W)) :=
  Finsupp.linearCombination ℤ fun t ↦
    if h : W ≤ cechOpenIntersection U (cechTupleSupport t) then
      (P.map (homOfLE h).op).hom.comp (LinearMap.proj t)
    else 0

/-- 一つのタプルの評価は切断の制限。 -/
theorem openCoverCechEvaluateAt_single {W : Opens X} {k : ℕ} {t : Fin k → ι}
    (h : W ≤ cechOpenIntersection U (cechTupleSupport t)) :
    openCoverCechEvaluateAt P U W k (Finsupp.single t 1) =
      (P.map (homOfLE h).op).hom.comp (LinearMap.proj t) := by
  simp [openCoverCechEvaluateAt, h]

/-- 台に現れる全タプルの交叉に入る開集合からは、更に制限できる。 -/
theorem openCoverCechEvaluateAt_restrict {W W' : Opens X} (h : W' ≤ W) {k : ℕ}
    (z : CechTupleChains ι k)
    (hz : ∀ t ∈ z.support, W ≤ cechOpenIntersection U (cechTupleSupport t))
    (a : FullCechCochains (openCoverCechDiagram P U) k) :
    (P.map (homOfLE h).op).hom (openCoverCechEvaluateAt P U W k z a) =
      openCoverCechEvaluateAt P U W' k z a := by
  unfold openCoverCechEvaluateAt
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro t ht
  have hW := hz t ht
  simp only [dite_eq_left hW, dite_eq_left (h.trans hW), LinearMap.comp_apply,
    LinearMap.proj_apply]
  congr 1
  change (P.map _ ≫ P.map _).hom _ = (P.map _).hom _
  rw [← P.map_comp]
  congr 2

/-- 境界の生成元の評価は、余境界のその生成元での評価。 -/
theorem openCoverCechEvaluateAt_boundary_single {W : Opens X} (k : ℕ)
    (t : Fin (k + 1) → ι) (h : W ≤ cechOpenIntersection U (cechTupleSupport t))
    (a : FullCechCochains (openCoverCechDiagram P U) k) :
    openCoverCechEvaluateAt P U W k (cechTupleBoundary k (Finsupp.single t 1)) a =
      openCoverCechEvaluateAt P U W (k + 1) (Finsupp.single t 1)
        (fullCechDifferential (openCoverCechDiagram P U) k a) := by
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [openCoverCechEvaluateAt_single P U h]
  change (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
      openCoverCechEvaluateAt P U W k (Finsupp.single (t ∘ i.succAbove) 1) a) =
    (P.map (homOfLE h).op).hom (fullCechDifferential (openCoverCechDiagram P U) k a t)
  rw [fullCechDifferential_apply]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [openCoverCechEvaluateAt_single P U
    (h.trans (cechOpenIntersection_antitone U (cechTupleSupport_face_subset t i)))]
  congr 1
  change (P.map _).hom _ = (P.map _ ≫ P.map _).hom _
  rw [← P.map_comp]
  congr 2

/-- 台に現れる交叉が指定開集合を含めば、境界と余境界は評価で対応する。 -/
theorem openCoverCechEvaluateAt_boundary {W : Opens X} (k : ℕ)
    (z : CechTupleChains ι (k + 1))
    (hz : ∀ t ∈ z.support, W ≤ cechOpenIntersection U (cechTupleSupport t))
    (a : FullCechCochains (openCoverCechDiagram P U) k) :
    openCoverCechEvaluateAt P U W k (cechTupleBoundary k z) a =
      openCoverCechEvaluateAt P U W (k + 1) z
        (fullCechDifferential (openCoverCechDiagram P U) k a) := by
  have he : ∑ t ∈ z.support, z t • Finsupp.single t 1 = z := by
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using z.sum_single
  calc
    _ = ∑ t ∈ z.support, z t • openCoverCechEvaluateAt P U W k
        (cechTupleBoundary k (Finsupp.single t 1)) a := by
      conv_lhs => rw [← he]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ t ∈ z.support, z t • openCoverCechEvaluateAt P U W (k + 1)
        (Finsupp.single t 1) (fullCechDifferential (openCoverCechDiagram P U) k a) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact congrArg (z t • ·) (openCoverCechEvaluateAt_boundary_single P U k t (hz t ht) a)
    _ = _ := by
      conv_rhs => rw [← he]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- 指定開集合での評価は、係数前層の射に自然。 -/
theorem openCoverCechEvaluateAt_naturality
    {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R} (η : P ⟶ Q) {W : Opens X} {k : ℕ}
    (z : CechTupleChains ι k)
    (hz : ∀ t ∈ z.support, W ≤ cechOpenIntersection U (cechTupleSupport t))
    (a : FullCechCochains (openCoverCechDiagram P U) k) :
    (η.app (Opposite.op W)).hom (openCoverCechEvaluateAt P U W k z a) =
      openCoverCechEvaluateAt Q U W k z
        (fullCechCochainsMap (openCoverCechCoefficientMap η U) k a) := by
  unfold openCoverCechEvaluateAt
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro t ht
  have hW := hz t ht
  simp only [dite_eq_left hW, LinearMap.comp_apply, LinearMap.proj_apply]
  congr 1
  exact congrArg (fun g ↦ g.hom (a t)) (η.naturality (homOfLE hW).op)

end SerrePositivity.AlgebraicGeometry
