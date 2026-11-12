module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import SerrePositivity.AlgebraicGeometry.CechTupleContraction
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComparison

/-!
概要：一つの頂点を挿入する制限が可逆な係数図式の Čech 縮約の準備。
方針：挿入の自然変換を明示し、その逆で先頭追加の評価を元の係数へ戻す。
規約：固定頂点の挿入による制限が同型である係数図式を扱う。
使われ方：共通アフィン細分の交叉上の増大完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped BigOperators
variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι]

/-- 有限集合に固定した頂点を挿入する関手。 -/
def cechInsertVertexFunctor (v : ι) : Finset ι ⥤ Finset ι where
  obj T := insert v T
  map h := homOfLE (Finset.insert_subset_insert v (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- 係数図式の制限による、頂点挿入の自然変換。 -/
def fullCechInsertVertexMap (D : Finset ι ⥤ ModuleCat R) (v : ι) :
    D ⟶ cechInsertVertexFunctor v ⋙ D where
  app T := D.map (homOfLE (Finset.subset_insert v T))
  naturality {T U} h := by
    dsimp only [Functor.comp_map]
    rw [← D.map_comp, ← D.map_comp]
    congr 1

/-- 各交叉で頂点挿入の制限が可逆なら、係数図式の自然同型になる。 -/
def fullCechInsertVertexIso (D : Finset ι ⥤ ModuleCat R) (v : ι)
    [∀ T, IsIso ((fullCechInsertVertexMap D v).app T)] :
    D ≅ cechInsertVertexFunctor v ⋙ D := by
  haveI := NatIso.isIso_of_isIso_app (fullCechInsertVertexMap D v)
  exact asIso (fullCechInsertVertexMap D v)

/-- タプルの先頭への挿入による、挿入後の係数での評価。 -/
def fullCechPrependVertex (D : Finset ι ⥤ ModuleCat R) (v : ι) (k : ℕ) :
    FullCechCochains D (k + 1) →ₗ[R]
      FullCechCochains (cechInsertVertexFunctor v ⋙ D) k :=
  LinearMap.pi fun t ↦
    (D.map (eqToHom (cechTupleSupport_cons v t))).hom.comp
      (LinearMap.proj (R := R)
        (φ := fun s : Fin (k + 1) → ι ↦ (D.obj (cechTupleSupport s) : Type _))
        (Fin.cons v t))

/-- 先頭挿入の評価は、係数図式の射に自然。 -/
theorem fullCechPrependVertex_naturality
    {D E : Finset ι ⥤ ModuleCat R} (η : D ⟶ E) (v : ι) (k : ℕ) :
    (fullCechCochainsMap (Functor.whiskerLeft (cechInsertVertexFunctor v) η) k).comp
        (fullCechPrependVertex D v k) =
      (fullCechPrependVertex E v k).comp (fullCechCochainsMap η (k + 1)) := by
  apply LinearMap.ext
  intro a
  funext t
  change (η.app (insert v (cechTupleSupport t))).hom
      ((D.map (eqToHom (cechTupleSupport_cons v t))).hom (a (Fin.cons v t))) =
    (E.map (eqToHom (cechTupleSupport_cons v t))).hom
      ((η.app (cechTupleSupport (Fin.cons v t))).hom (a (Fin.cons v t)))
  have h := congrArg (fun f ↦ f.hom (a (Fin.cons v t)))
    (η.naturality (eqToHom (cechTupleSupport_cons v t)))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- 挿入の制限の逆で係数を戻した、縮約の候補。 -/
def fullCechSplitVertexContraction (D : Finset ι ⥤ ModuleCat R) (v : ι)
    [∀ T, IsIso ((fullCechInsertVertexMap D v).app T)] (k : ℕ) :
    FullCechCochains D (k + 1) →ₗ[R] FullCechCochains D k :=
  (fullCechCochainsMap (fullCechInsertVertexIso D v).inv k).comp
    (fullCechPrependVertex D v k)

/-- 頂点挿入まで台を広げる鎖写像の転置。 -/
def fullCechInsertTranspose (D : Finset ι ⥤ ModuleCat R) (v : ι)
    {k l : ℕ} (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k) :
    FullCechCochains D k →ₗ[R]
      FullCechCochains (cechInsertVertexFunctor v ⋙ D) l :=
  LinearMap.pi fun t ↦
    fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (P (Finsupp.single t 1))

/-- 挿入まで広げる写像の前に、台を保つ写像を合成する場合の転置。 -/
theorem fullCechInsertTranspose_comp_preserving_left
    (D : Finset ι ⥤ ModuleCat R) (v : ι) {k l m : ℕ}
    (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k)
    (Q : CechTupleChains ι m →ₗ[ℤ] CechTupleChains ι l)
    (hP : ∀ t u, u ∈ (P (Finsupp.single t 1)).support →
      cechTupleSupport u ⊆ cechTupleSupport t)
    (hQ : ∀ t u, u ∈ (Q (Finsupp.single t 1)).support →
      cechTupleSupport u ⊆ insert v (cechTupleSupport t)) :
    fullCechInsertTranspose D v (P.comp Q) =
      (fullCechInsertTranspose D v Q).comp (fullCechTranspose D P) := by
  apply LinearMap.ext
  intro a
  funext t
  let z := Q (Finsupp.single t 1)
  change fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (P z) a =
    fullCechEvaluateAt D l (insert v (cechTupleSupport t)) z (fullCechTranspose D P a)
  have hz : ∑ u ∈ z.support, z u • Finsupp.single u 1 = z := by
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using z.sum_single
  calc
    _ = ∑ u ∈ z.support, z u •
        fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (P (Finsupp.single u 1)) a := by
      conv_lhs => rw [← hz]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = _ := by
      conv_rhs => unfold fullCechEvaluateAt
      rw [Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro u hu
      have hs := hQ t u hu
      simp only [dite_eq_left hs, LinearMap.comp_apply, LinearMap.proj_apply]
      change z u • fullCechEvaluateAt D k (insert v (cechTupleSupport t))
          (P (Finsupp.single u 1)) a =
        z u • (D.map (homOfLE hs)).hom
          (fullCechEvaluateAt D k (cechTupleSupport u) (P (Finsupp.single u 1)) a)
      exact congrArg (z u • ·)
        (fullCechEvaluateAt_restrict D hs _ (fun w hw ↦ hP u w hw) a).symm

/-- 台を保つ写像の前に、挿入まで広げる写像を合成する場合の転置。 -/
theorem fullCechInsertTranspose_comp_preserving_right
    (D : Finset ι ⥤ ModuleCat R) (v : ι) {k l m : ℕ}
    (P : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k)
    (Q : CechTupleChains ι m →ₗ[ℤ] CechTupleChains ι l)
    (hP : ∀ t u, u ∈ (P (Finsupp.single t 1)).support →
      cechTupleSupport u ⊆ insert v (cechTupleSupport t))
    (hQ : ∀ t u, u ∈ (Q (Finsupp.single t 1)).support →
      cechTupleSupport u ⊆ cechTupleSupport t) :
    fullCechInsertTranspose D v (P.comp Q) =
      (fullCechTranspose (cechInsertVertexFunctor v ⋙ D) Q).comp
        (fullCechInsertTranspose D v P) := by
  apply LinearMap.ext
  intro a
  funext t
  let z := Q (Finsupp.single t 1)
  change fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (P z) a =
    fullCechEvaluateAt (cechInsertVertexFunctor v ⋙ D) l (cechTupleSupport t) z
      (fullCechInsertTranspose D v P a)
  have hz : ∑ u ∈ z.support, z u • Finsupp.single u 1 = z := by
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using z.sum_single
  calc
    _ = ∑ u ∈ z.support, z u •
        fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (P (Finsupp.single u 1)) a := by
      conv_lhs => rw [← hz]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = _ := by
      conv_rhs => unfold fullCechEvaluateAt
      rw [Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro u hu
      have hs := hQ t u hu
      simp only [dite_eq_left hs, LinearMap.comp_apply, LinearMap.proj_apply]
      change z u • fullCechEvaluateAt D k (insert v (cechTupleSupport t))
          (P (Finsupp.single u 1)) a =
        z u • (D.map (homOfLE (Finset.insert_subset_insert v hs))).hom
          (fullCechEvaluateAt D k (insert v (cechTupleSupport u)) (P (Finsupp.single u 1)) a)
      exact congrArg (z u • ·)
        (fullCechEvaluateAt_restrict D (Finset.insert_subset_insert v hs) _
          (fun w hw ↦ hP u w hw) a).symm

/-- 挿入を許す転置は鎖写像の和を保つ。 -/
theorem fullCechInsertTranspose_add (D : Finset ι ⥤ ModuleCat R) (v : ι)
    {k l : ℕ} (P Q : CechTupleChains ι l →ₗ[ℤ] CechTupleChains ι k) :
    fullCechInsertTranspose D v (P + Q) =
      fullCechInsertTranspose D v P + fullCechInsertTranspose D v Q := by
  apply LinearMap.ext
  intro a
  funext t
  change (fullCechEvaluateAt D k (insert v (cechTupleSupport t)))
      ((P + Q) (Finsupp.single t 1)) a =
    (fullCechEvaluateAt D k (insert v (cechTupleSupport t))) (P (Finsupp.single t 1)) a +
      (fullCechEvaluateAt D k (insert v (cechTupleSupport t))) (Q (Finsupp.single t 1)) a
  simp only [LinearMap.add_apply, map_add]

/-- 恒等写像の挿入を許す転置は、挿入による係数の制限。 -/
theorem fullCechInsertTranspose_id (D : Finset ι ⥤ ModuleCat R) (v : ι) (k : ℕ) :
    fullCechInsertTranspose D v (LinearMap.id : CechTupleChains ι k →ₗ[ℤ] _) =
      fullCechCochainsMap (fullCechInsertVertexMap D v) k := by
  apply LinearMap.ext
  intro a
  funext t
  change fullCechEvaluateAt D k (insert v (cechTupleSupport t)) (Finsupp.single t 1) a = _
  rw [fullCechEvaluateAt_single D (Finset.subset_insert v (cechTupleSupport t))]
  rfl

/-- 先頭追加の像の台は、元の台にその頂点を追加した集合に収まる。 -/
theorem cechTuplePrepend_support_insert (v : ι) (k : ℕ) :
    ∀ t u, u ∈ (cechTuplePrepend v k (Finsupp.single t 1)).support →
      cechTupleSupport u ⊆ insert v (cechTupleSupport t) := by
  intro t u hu
  have he : u = Fin.cons v t := by
    simpa only [cechTuplePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] using hu
  subst u
  exact (cechTupleSupport_cons v t).le

/-- 先頭追加を転置したものは、係数図式への先頭挿入の評価。 -/
theorem fullCechInsertTranspose_prepend (D : Finset ι ⥤ ModuleCat R) (v : ι) (k : ℕ) :
    fullCechInsertTranspose D v (cechTuplePrepend v k) = fullCechPrependVertex D v k := by
  apply LinearMap.ext
  intro a
  funext t
  change fullCechEvaluateAt D (k + 1) (insert v (cechTupleSupport t))
      (cechTuplePrepend v k (Finsupp.single t 1)) a = _
  simp only [cechTuplePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [fullCechEvaluateAt_single D (cechTupleSupport_cons v t).le]
  have he : (homOfLE (cechTupleSupport_cons v t).le :
      cechTupleSupport (Fin.cons v t) ⟶ insert v (cechTupleSupport t)) =
        eqToHom (cechTupleSupport_cons v t) := Subsingleton.elim _ _
  rw [he]
  rfl

/-- 係数図式付きの先頭挿入と余境界の反交換式。同型性の仮定は不要。 -/
theorem fullCechPrependVertex_identity (D : Finset ι ⥤ ModuleCat R) (v : ι) (k : ℕ) :
    (fullCechPrependVertex D v (k + 1)).comp (fullCechDifferential D (k + 1)) +
      (fullCechDifferential (cechInsertVertexFunctor v ⋙ D) k).comp
        (fullCechPrependVertex D v k) = fullCechCochainsMap (fullCechInsertVertexMap D v) (k + 1) := by
  rw [← fullCechInsertTranspose_prepend D v (k + 1),
    ← fullCechInsertTranspose_prepend D v k,
    ← fullCechTranspose_boundary D (k + 1),
    ← fullCechTranspose_boundary (cechInsertVertexFunctor v ⋙ D) k,
    ← fullCechInsertTranspose_comp_preserving_left D v _ _
      (cechTupleBoundary_preservesSupport (k + 1)) (cechTuplePrepend_support_insert v (k + 1)),
    ← fullCechInsertTranspose_comp_preserving_right D v _ _
      (cechTuplePrepend_support_insert v k) (cechTupleBoundary_preservesSupport k),
    ← fullCechInsertTranspose_add, cechTupleBoundary_prepend, fullCechInsertTranspose_id]

/-- 挿入の制限が同型なら、係数図式の全タプル Čech コチェインは縮約する。 -/
theorem fullCechSplitVertexContraction_identity (D : Finset ι ⥤ ModuleCat R) (v : ι)
    [∀ T, IsIso ((fullCechInsertVertexMap D v).app T)] (k : ℕ) :
    (fullCechSplitVertexContraction D v (k + 1)).comp (fullCechDifferential D (k + 1)) +
      (fullCechDifferential D k).comp (fullCechSplitVertexContraction D v k) = LinearMap.id := by
  let e := fullCechInsertVertexIso D v
  calc
    _ = (fullCechCochainsMap e.inv (k + 1)).comp
        ((fullCechPrependVertex D v (k + 1)).comp (fullCechDifferential D (k + 1)) +
          (fullCechDifferential (cechInsertVertexFunctor v ⋙ D) k).comp
            (fullCechPrependVertex D v k)) := by
      rw [LinearMap.comp_add]
      refine congrArg₂ (· + ·) rfl ?_
      apply LinearMap.ext
      intro a
      exact (LinearMap.congr_fun (fullCechCochainsMap_comp_differential e.inv k)
        (fullCechPrependVertex D v k a)).symm
    _ = LinearMap.id := by
      rw [fullCechPrependVertex_identity]
      apply LinearMap.ext
      intro a
      funext t
      change (e.inv.app (cechTupleSupport t)).hom
        ((e.hom.app (cechTupleSupport t)).hom (a t)) = a t
      have he : e.hom.app (cechTupleSupport t) ≫ e.inv.app (cechTupleSupport t) = 𝟙 _ :=
        congrArg (fun η ↦ η.app (cechTupleSupport t)) e.hom_inv_id
      have h := congrArg (fun f ↦ f.hom (a t)) he
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using h

end SerrePositivity.AlgebraicGeometry
