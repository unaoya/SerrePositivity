module
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementComponents
public import SerrePositivity.InfinityCategories.Derived.DGSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGSimplexComponentExt
public import SerrePositivity.InfinityCategories.Derived.DGTriangleSourceRefinement

/-! # 一般閉始点細分と既存の三角形細分の厳密一致

概要：一般次元の構成は、二次元では元の三辺・三角 cochain による細分と同じ実単体。
方針：全体集合の三角成分と二点集合の三辺へ分け、全成分を直接比較する。
規約：同じ指定閉射を保つ。使われ方：高次の面を既存の細分頂点脚へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]


/-- 一般閉始点細分は、二次元では既存の三角形細分そのもの。 -/
lemma dgSimplexInitialRefinement_triangle (t : Simplex A D 2) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) (t.obj 0)) :
    dgSimplexInitialRefinement A D t q s = dgSimplexSourceRefinement t q s := by
  apply Simplex.ext
  apply dgSimplexData_ext_of_components A D
  · intro i
    fin_cases i <;> rfl
  · intro I a b k hI ha hb hk
    by_cases hc : I.card = 3
    · have h := three_eq_univ I hc
      subst I
      have ha' : a = 0 :=
        ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
      have hb' : b = 2 :=
        hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
      have hk' : k = -1 := by simpa using hk
      subst ha' hb' hk'
      rfl
    · have hle := Finset.card_le_univ I
      simp only [Fintype.card_fin] at hle
      have hc2 : I.card = 2 := by omega
      have hab : a < b := dgSimplexIndex_endpoints_lt I a b hI ha hb
      have hpair : I = {a, b} := Index.eq_pair hc2
        (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
      have hk' : k = 0 := by omega
      subst hk'
      fin_cases a <;> fin_cases b <;> norm_num at hab
      all_goals subst I; rfl

end SerrePositivity.InfinityCategories
