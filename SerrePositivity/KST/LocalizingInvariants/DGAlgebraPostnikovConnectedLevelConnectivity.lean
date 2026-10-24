module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectedLevelPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPullbackQuotientAt

/-!
概要：元の未切断の源から構成した実レベル表示への射は、各段で (n+1)-connected。
方針：像模型への射影を切断範囲で同型比較し、元の像射影の全射性を回収する。
規約：π₀ を含む全整数群で判定する。使われ方：元の射を保持する連結なレベル表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
open ProExcision
attribute [local instance] source_nonpositive
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

def comparison (i : ℕ) : ((middle R X n hn).obj i).obj ⟶
    (PostnikovImagePro.middle R X n hn).obj i :=
  connectiveCoverInclusion R ((rawMiddle R X n hn).obj i) ≫
    HomotopyPullbackModel.left R ((PostnikovImagePro.right R X n hn).app i)
      ((PostnikovImagePro.targetQuotient R X n).app i)

lemma comparison_quasiIsoAt (i : ℕ) (z : ℤ) (hz : -(n + 1) ≤ z) (hz0 : z ≤ 0) :
    QuasiIsoAt (comparison R X n hn i).hom z := by
  have hc : QuasiIsoAt (connectiveCoverInclusion R ((rawMiddle R X n hn).obj i)).hom z := by
    change QuasiIsoAt (((rawMiddle R X n hn).obj i).X.ιTruncLE 0) z
    exact CochainComplex.quasiIsoAt_ιTruncLE _ 0 z hz0
  have hp := homotopyPullback_postnikov_left_quasiIsoAt R (X.obj i).right.obj (n + 1)
    ((PostnikovImagePro.right R X n hn).app i) z hz
  exact quasiIsoAt_comp _ _ z (hφ := hc) (hφ' := hp)

lemma left_comparison (i : ℕ) :
    ((left R X n hn).app i).hom ≫ comparison R X n hn i =
      (PostnikovImagePro.sourceQuotient R X n).app i ≫ (PostnikovImagePro.left R X n hn).app i := by
  change connectiveCoverLift R ((rawLeft R X n hn).app i) ≫
    (connectiveCoverInclusion R ((rawMiddle R X n hn).obj i) ≫ _) = _
  rw [← Category.assoc, connectiveCoverLift_inclusion]
  exact HomotopyPullbackModel.squareLiftApp_left R _ _ _ _ _ i

lemma left_group_properties (i : ℕ) (j : ℤ) (hj0 : 0 ≤ j) (hjn : j ≤ n + 1) :
    (j < n + 1 → Function.Injective ((groups R j).map ((left R X n hn).app i).hom).hom) ∧
      Function.Surjective ((groups R j).map ((left R X n hn).app i).hom).hom := by
  have hp := groups_map_isIso_of_quasiIsoAt R (comparison R X n hn i) j
    (comparison_quasiIsoAt R X n hn i (-j) (by omega) (by omega))
  have hpb := ConcreteCategory.bijective_of_isIso ((groups R j).map (comparison R X n hn i))
  have hq := postnikovQuotient_groups_isIso R (X.obj i).left.obj (n + 1) j hjn
  have hqb := ConcreteCategory.bijective_of_isIso
    (by exact (groups R j).map (postnikovQuotient R (X.obj i).left.obj (n + 1)))
  have hsq := congrArg ((groups R j).map) (left_comparison R X n hn i)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hsq
  refine ⟨?_, ?_⟩
  · intro hj x y hxy
    apply hqb.1
    apply (PostnikovImagePro.left_connected R X n hn i).1 j hj
    have ha := congrArg (fun t => t.hom x) hsq
    have hb := congrArg (fun t => t.hom y) hsq
    exact ha.symm.trans ((congrArg ((groups R j).map (comparison R X n hn i)).hom hxy).trans hb)
  · intro y
    obtain ⟨x, hx⟩ := (PostnikovImagePro.left_connected R X n hn i).2 j hjn
      (((groups R j).map (comparison R X n hn i)).hom y)
    obtain ⟨z, hz⟩ := hqb.2 x
    refine ⟨z, hpb.1 ?_⟩
    have ha := congrArg (fun t => t.hom z) hsq
    exact ha.trans ((congrArg ((groups R j).map ((PostnikovImagePro.left R X n hn).app i)).hom
      hz).trans hx)

lemma left_groups_bijective_negative (i : ℕ) (j : ℤ) (hj : j < 0) :
    Function.Bijective ((groups R j).map ((left R X n hn).app i).hom).hom := by
  have hsource : ((source R X).obj i).obj.X.IsStrictlyLE 0 := ((source R X).obj i).property
  have hmiddle : ((middle R X n hn).obj i).obj.X.IsStrictlyLE 0 :=
    ((middle R X n hn).obj i).property
  have : Subsingleton ((groups R j).obj ((source R X).obj i).obj) :=
    groups_subsingleton_of_homology_zero R _ j
      (((source R X).obj i).obj.X.isZero_of_isLE 0 (-j) (by omega))
  have : Subsingleton ((groups R j).obj ((middle R X n hn).obj i).obj) :=
    groups_subsingleton_of_homology_zero R _ j
      (((middle R X n hn).obj i).obj.X.isZero_of_isLE 0 (-j) (by omega))
  exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

lemma left_connected (i : ℕ) : IsConnected R ((left R X n hn).app i).hom (n + 1) := by
  constructor
  · intro j hj
    by_cases hj0 : 0 ≤ j
    · exact (left_group_properties R X n hn i j hj0 hj.le).1 hj
    · exact (left_groups_bijective_negative R X n hn i j (by omega)).1
  · intro j hj
    by_cases hj0 : 0 ≤ j
    · exact (left_group_properties R X n hn i j hj0 hj).2
    · exact (left_groups_bijective_negative R X n hn i j (by omega)).2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
