module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Almost.AlmostConnectivity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid

/-! # 生成元ごとの almost 零性

## 概要
BS 著者版 Theorem 10.9 の証明に使う有限生成イデアルの almost 零性の判定。

## 方針
零化イデアルによる導来完備な商へ、二つの perfectoid 商の完備テンソルから写す。

## 規約
複体は導来 p 完備、各次数の零化は通常の加群の零化。

## 使われ方
almost purity の主イデアルへの帰着。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.BhattScholze.Almost
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

include hR in
private theorem annihilator_isModuleComplete (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R (p : R) M) :
    IsModuleComplete R (p : R) (ModuleCat.of R (Module.annihilator R M)) := by
  have hr := (isModuleComplete_iff_recurrence_bijective R (p : R) (ModuleCat.of R R)).mp
    (hR.isModuleComplete_algebra R R p)
  have hm := (isModuleComplete_iff_recurrence_bijective R (p : R) M).mp hM
  apply (isModuleComplete_iff_recurrence_bijective R (p : R) _).mpr
  constructor
  · intro x y hxy
    have he : (fun n ↦ (x n).val) = (fun n ↦ (y n).val) := hr.injective
      (congrArg (fun z n ↦ (z n).val) hxy)
    funext n
    exact Subtype.ext (congrFun he n)
  · intro y
    obtain ⟨x, hx⟩ := hr.surjective (fun n ↦ (y n).val)
    have hxAnn (n : ℕ) : x n ∈ Module.annihilator R M := by
      apply Module.mem_annihilator.mpr
      intro m
      let g := LinearMap.toSpanSingleton R M m
      have hg : adicRecurrenceMap (p : R) (fun n ↦ g (x n)) = 0 := by
        funext n
        change g (x n) - (p : R) • g (x (n + 1)) = 0
        rw [← map_smul, ← map_sub]
        exact (congrArg g (congrFun hx n)).trans (Module.mem_annihilator.mp (y n).property m)
      exact congrFun (hm.injective (hg.trans (map_zero _).symm)) n
    refine ⟨fun n ↦ ⟨x n, hxAnn n⟩, ?_⟩
    funext n
    exact Subtype.ext (congrFun hx n)

private def quotientPerfdMap_factor (J : Ideal R)
    {A : Type u} [CommRing A] [Algebra R A]
    (h : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R J p hR →ₐ[R] A where
  toRingHom := (Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A)
    (fun _ hx ↦ h hx)).comp
      (RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm.toRingHom
  commutes' x := by
    change Ideal.Quotient.lift (perfectoidKernel p R hR J) (algebraMap R A)
      (fun _ hx ↦ h hx)
      ((RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm
        (quotientPerfdMap p R hR J x)) = _
    rw [show quotientPerfdMap p R hR J x =
        RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)
          (Ideal.Quotient.mk (perfectoidKernel p R hR J) x) from rfl,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

private theorem perfectoidKernel_sup_le_ker {I J : Ideal R} {A : Type u} [CommRing A] [Algebra R A]
    (hA : IsModuleComplete R (p : R) (ModuleCat.of R A))
    (hI : perfectoidKernel p R hR I ≤ RingHom.ker (algebraMap R A))
    (hJ : perfectoidKernel p R hR J ≤ RingHom.ker (algebraMap R A)) :
    perfectoidKernel p R hR (I ⊔ J) ≤ RingHom.ker (algebraMap R A) := by
  let S := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR
  let T := _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R J p hR
  let D := S ⊗[R] T
  let C := PrincipalCompletionH0 D (p : D)
  let : CommRing C := principalCompletionCommRing D (p : D)
  let d := principalCompletionUnitRingHom D (p : D)
  let e : D →ₐ[R] A := Algebra.TensorProduct.lift (quotientPerfdMap_factor p R hR I hI)
    (quotientPerfdMap_factor p R hR J hJ) (fun _ _ ↦ Commute.all _ _)
  let : Algebra D A := e.toRingHom.toAlgebra
  let : IsScalarTower R D A := IsScalarTower.of_algebraMap_eq (fun x ↦ (e.commutes x).symm)
  have ha : IsModuleComplete D (p : D) (ModuleCat.of D A) := by
    simpa only [map_natCast] using (isModuleComplete_algebraMap_iff R D (p : R) A).mpr hA
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have hc : IsIntegralPerfectoid C p :=
    isIntegralPerfectoid_of_ringEquiv p (completedTensorH0PrincipalRingEquiv R p S T)
      (integralPerfectoid_completedTensorH0_isIntegralPerfectoid p R S T hR
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R I p hR).1
        (_root_.SerrePositivity.BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization R J p hR).1)
  have hkill : I ⊔ J ≤ RingHom.ker (d.comp (algebraMap R D)) := by
    apply sup_le
    · intro x hx
      have hx' : algebraMap R S x = 0 := le_perfectoidKernel p R hR I hx
      change d (algebraMap R D x) = 0
      rw [IsScalarTower.algebraMap_apply R S D, hx', map_zero, map_zero]
    · intro x hx
      have hx' : algebraMap R T x = 0 := le_perfectoidKernel p R hR J hx
      change d (algebraMap R D x) = 0
      rw [← (Algebra.TensorProduct.includeRight : T →ₐ[R] D).commutes x,
        hx', map_zero, map_zero]
  have hK := perfectoidKernel_le p R hR (I ⊔ J) hc _ hkill
  obtain ⟨g, hg, _⟩ := principalCompletion_existsUnique_ringHom D (p : D) A e.toRingHom ha
  intro x hx
  have hcx : d (algebraMap R D x) = 0 := hK hx
  have he := DFunLike.congr_fun hg (algebraMap R D x)
  change g (d (algebraMap R D x)) = e (algebraMap R D x) at he
  rw [hcx, map_zero, e.commutes] at he
  exact he.symm

/-- 二つの核による almost 零性を、その和のイデアルの almost 零性にまとめる。 -/
theorem isAlmostZero_perfectoidKernel_sup (I J : Ideal R) (M : ModuleCat.{u} R)
    (hM : IsModuleComplete R (p : R) M)
    (hI : SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR I) M)
    (hJ : SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J) M) :
    SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR (I ⊔ J)) M := by
  let A := Module.annihilator R M
  have hA := annihilator_isModuleComplete p R hR M hM
  have hR' := hR.isModuleComplete_algebra R R p
  have hc := isModuleComplete_coker R (p : R) (M := ModuleCat.of R A) A.subtype hA hR'
  rw [Submodule.range_subtype] at hc
  have hk : RingHom.ker (algebraMap R (R ⧸ A)) = A := Ideal.mk_ker
  change perfectoidKernel p R hR (I ⊔ J) ≤ A
  change perfectoidKernel p R hR I ≤ A at hI
  change perfectoidKernel p R hR J ≤ A at hJ
  rw [← hk] at hI hJ ⊢
  exact perfectoidKernel_sup_le_ker p R hR hc hI hJ

/--
## 概要
有限生成イデアルによる almost 零性を生成元ごとに判定する。
BS 著者版 Theorem 10.9 の証明の主イデアルへの帰着で使う。

## 方針
コホモロジー加群の零化イデアルで割り、perfectoid な二つの商の完備テンソルを使う。

## 規約
コホモロジー次数を用いる。生成族が空の場合を含む。

## 使われ方
BS 著者版 Remark 10.7 に続く almost 零性の比較。
-/
theorem isAlmostZero_iff_forall_gen (J : Ideal R) {r : ℕ} (f : Fin r → R)
    (hf : J = Ideal.span (Set.range f)) (M : DVertex R) (hM : SerrePositivity.DerivedInfinity.IsPComplete p R M) :
    _root_.SerrePositivity.BhattScholze.Almost.IsAlmostZeroComplex p R hR J M ↔ ∀ i, _root_.SerrePositivity.BhattScholze.Almost.IsAlmostZeroComplex p R hR (Ideal.span {f i}) M := by
  classical
  constructor
  · intro h i n
    exact (perfectoidKernel_mono p R hR _ (by
      rw [hf]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨i, rfl⟩))).trans (h n)
  · intro h n
    let N := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R n M
    have hn : IsModuleComplete R (p : R) N :=
      isComplete_homology_isModuleComplete R (p : R) _ hM n
    have hs (s : Finset R) (hf' : (s : Set R) ⊆ Set.range f) :
        SerrePositivity.Almost.IsAlmostZero
          (perfectoidKernel p R hR (Ideal.span (s : Set R))) N := by
      induction s using Finset.induction_on with
      | empty =>
        have hker : RingHom.ker (RingHom.id R) = ⊥ :=
          (RingHom.ker_eq_bot_iff_eq_zero (RingHom.id R)).mpr (fun _ hx ↦ hx)
        have hz : perfectoidKernel p R hR (⊥ : Ideal R) ≤ ⊥ := by
          rw [← hker]
          exact perfectoidKernel_le p R hR _ hR (RingHom.id R) bot_le
        simpa only [Finset.coe_empty, Ideal.span_empty,
          SerrePositivity.Almost.IsAlmostZero] using
          (hz.trans (bot_le : (⊥ : Ideal R) ≤ Module.annihilator R N))
      | insert a s has ih =>
        obtain ⟨i, hi⟩ := hf' (Finset.mem_insert_self a s)
        have ha := h i n
        rw [hi] at ha
        rw [Finset.coe_insert, Set.insert_eq, Ideal.span_union]
        exact isAlmostZero_perfectoidKernel_sup p R hR _ _ N hn ha
          (ih (fun _ hx => hf' (Finset.mem_insert_of_mem hx)))
    have he : ((Finset.univ.image f : Finset R) : Set R) = Set.range f := by
      simp
    rw [hf, ← he]
    exact hs _ (he ▸ Set.Subset.rfl)

end SerrePositivity.BhattScholze.Almost

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 10.9" (partial := component) "主イデアルへの帰着、分裂比較環、整閉包の完備化（BS-W13）。組み立ては A6・A7 待ち ／ 11-10 更新 ／ 11-12：integralClosureCompletion_isModuleComplete は Thm 10.11 の部品なので列から外した"] _root_.SerrePositivity.BhattScholze.Almost.isAlmostZero_iff_forall_gen
