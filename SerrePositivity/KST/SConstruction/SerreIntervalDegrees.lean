module
public import SerrePositivity.KST.SConstruction.SerreIntervalContractionValues

/-! # 元の鎖区間の全次数の生成元による判定
概要：鎖区間は次数零と −1 だけを持ち、元の二端点と辺で線形射を判定できる。
方針：元の直和の次数ごとの比較と、単位・disk の生成元の普遍性を使う。
規約：別の基底模型へ置換しない。使われ方：max connection の全斉次成分の法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖区間の零・−1 以外の次数は零対象。 -/
lemma serreInterval_isZero_X (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ -1) :
    IsZero ((serreInterval A).X n) := by
  have hU := isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) n h₀
  have hD := isZero_double_X (𝟙 (𝟙_ (ModuleCat A)))
    (show (ComplexShape.up ℤ).Rel (-1) (-1 + 1) by simp) n h₁ (by omega)
  have h := (biprod_isZero_iff ((𝟙_ (Complex A)).X n) ((complexDisk A (-1)).X n)).2 ⟨hU, hD⟩
  exact h.of_iso (biprodXIso (𝟙_ (Complex A)) (complexDisk A (-1)) n)

/-- 元の二端点での値が等しい次数零の線形射は等しい。 -/
lemma serreInterval_degree_zero_ext {V : ModuleCat.{u} A}
    {f g : (serreInterval A).X 0 ⟶ V}
    (h₀ : f (cycleFromUnit _ (serreIntervalZero A)).val =
      g (cycleFromUnit _ (serreIntervalZero A)).val)
    (h₁ : f (cycleFromUnit _ (serreIntervalOne A)).val =
      g (cycleFromUnit _ (serreIntervalOne A)).val) : f = g := by
  apply (cancel_epi (biprodXIso (𝟙_ (Complex A)) (complexDisk A (-1)) 0).inv).1
  apply biprod.hom_ext'
  · rw [← Category.assoc, ← Category.assoc, inl_biprodXIso_inv]
    apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv).1
    apply (moduleElementEquiv A V).injective
    exact h₀
  · rw [← Category.assoc, ← Category.assoc, inr_biprodXIso_inv]
    apply (cancel_epi (complexDiskX₁ A (-1)).inv).1
    apply (moduleElementEquiv A V).injective
    have h := complexDisk_upper_apply A (-1)
      (biprod.inr : complexDisk A (-1) ⟶ serreInterval A)
    change (biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0
        ((complexDiskX₁ A (-1)).inv (1 : A)) =
      (serreInterval A).d (-1) 0 (serreIntervalEdge A) at h
    rw [serreIntervalEdge_d] at h
    change f ((biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0 _) =
      g ((biprod.inr : complexDisk A (-1) ⟶ serreInterval A).f 0 _)
    refine (congrArg (fun x => f x) h).trans ?_
    refine Eq.trans ?_ (congrArg (fun x => g x) h).symm
    simp only [map_sub, h₀, h₁]

/-- 元の辺での値が等しい次数 −1 の線形射は等しい。 -/
lemma serreInterval_degree_neg_one_ext {V : ModuleCat.{u} A}
    {f g : (serreInterval A).X (-1) ⟶ V}
    (he : f (serreIntervalEdge A) = g (serreIntervalEdge A)) : f = g := by
  apply (cancel_epi (biprodXIso (𝟙_ (Complex A)) (complexDisk A (-1)) (-1)).inv).1
  apply biprod.hom_ext'
  · exact (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) (-1) (by omega)).eq_of_src _ _
  · rw [← Category.assoc, ← Category.assoc, inr_biprodXIso_inv]
    apply (cancel_epi (complexDiskX₀ A (-1)).inv).1
    apply (moduleElementEquiv A V).injective
    exact he

/-- 元の一端点への収縮は、同じ辺を零に写す。 -/
lemma serreIntervalContraction_edge :
    (serreIntervalContraction A).v (-1) (-2) (by omega) (serreIntervalEdge A) = 0 := by
  have := ModuleCat.subsingleton_of_isZero (serreInterval_isZero_X A (-2) (by omega) (by omega))
  exact Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
