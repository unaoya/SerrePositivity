module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralRefinedData
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementPositiveFaces

/-! # 一般実細分ホーンの正番号面と元の指定面の閉細分

概要：新ホーンの全正番号面は、元の同じ指定面の同じ閉始点細分である。
方針：全回収データの一致と零固定の引き戻し整合性を使う。
規約：端点等式による閉射の輸送も明示。使われ方：高次 over 単体の回収と共有面の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 元の回収対象族を使う、各指定面の実単体。 -/
def dgGeneralLastHornCanonicalFace (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
    Simplex A D (n + 1) :=
  dgPartialSimplexHornFace (HornData.knownData σ) (Fin.last (n + 2))
    (fun I hf hm => dgGeneralLastHornKnown_equation σ I hf hm) j hj

/-- 元の回収対象族による各面は、元の実ホーン面と厳密に同じ。 -/
lemma dgGeneralLastHornCanonicalFace_eq (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) :
    dgGeneralLastHornCanonicalFace σ j hj = σ.app _ (horn.face (Fin.last (n + 2)) j hj) := by
  apply Simplex.ext
  exact HornData.knownData_pullback_face σ j hj

variable (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 全ての新しい正番号面は、元の同じ指定面を同じ実閉射で細分したもの。 -/
lemma dgGeneralLastHornSourceRefinement_value_positive (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) (hj₀ : j ≠ 0) :
    (dgGeneralLastHornSourceRefinement σ q s).app _ (horn.face (Fin.last (n + 2)) j hj) =
      dgSimplexInitialRefinement A D (dgGeneralLastHornCanonicalFace σ j hj) q
        (dgClosedTargetTransport A D s
          (congrArg (HornData.knownData σ).obj (dgPositiveCoface_zero j hj₀).symm)) := by
  apply Simplex.ext
  refine (HornData.knownData_pullback_face _ j hj).symm.trans ?_
  refine (congrArg (fun t : SimplexData A D (n + 2) =>
    t.pullback j.succAboveOrderEmb.toOrderHom)
      (dgGeneralLastHornSourceRefinement_knownData σ q s)).trans ?_
  exact dgSimplexDataInitialRefinement_pullback_fixed_zero A D (HornData.knownData σ) q s
    j.succAboveOrderEmb.toOrderHom j.succAboveOrderEmb.injective (dgPositiveCoface_zero j hj₀)

/-- 正番号面の米田表示も、同じ指定単体の閉細分を厳密に与える。 -/
lemma dgGeneralLastHornSourceRefinement_face_positive (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) (hj₀ : j ≠ 0) :
    horn.ι (Fin.last (n + 2)) j hj ≫ dgGeneralLastHornSourceRefinement σ q s =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgSimplexInitialRefinement A D (dgGeneralLastHornCanonicalFace σ j hj) q
          (dgClosedTargetTransport A D s
            (congrArg (HornData.knownData σ).obj (dgPositiveCoface_zero j hj₀).symm))) := by
  apply (SSet.yonedaEquiv (X := dgNerve A D)).injective
  rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι, Equiv.apply_symm_apply]
  exact dgGeneralLastHornSourceRefinement_value_positive σ q s j hj hj₀

end SerrePositivity.InfinityCategories
