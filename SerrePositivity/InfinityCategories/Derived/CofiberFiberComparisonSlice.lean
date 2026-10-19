module
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonJoin
public import SerrePositivity.InfinityCategories.DGNerve.RebaseCone
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! # 標準 cofiber 錐から標準 fiber 錐への実際の辺

概要：貼り合わせた join 写像を curry し、同じ cospan 上の slice の比較辺を作る。
方針：二つの四角形の cospan を同定し、join の端点の等式から始点と終点を確認する。
規約：普遍性による選択に依存しない。使われ方：D7 の極限性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

/-- Curry した比較写像の端点は、join の端点への制限で定まる。 -/
lemma sliceOverCurry_vertex_of_join {K X : SSet.{u}} {p : K ⟶ X}
    (F : join (Δ[1] : SSet.{u}) K ⟶ X) (hF : joinInr Δ[1] K ≫ F = p)
    (i : Fin 2) (c : JoinCone p)
    (hc : joinMap (SSet.stdSimplex.δ i) (𝟙 K) ≫ F = c.val) :
    (sliceOver p).δ i (SSet.yonedaEquiv (sliceOverCurry F hF)) = c := by
  have hm : SSet.stdSimplex.δ i ≫ sliceOverCurry F hF = SSet.yonedaEquiv.symm c := by
    rw [sliceOverCurry_precomp]
    let d : JoinCone p := ⟨joinMap (SSet.stdSimplex.δ i) (𝟙 K) ≫ F, by
      rw [← Category.assoc, joinInr_joinMap, Category.id_comp, hF]⟩
    have hd : d = c := Subtype.ext hc
    exact (sliceOverCurry_yoneda 0 d).trans (congrArg SSet.yonedaEquiv.symm hd)
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp, hm]
  exact (SSet.yonedaEquiv (X := sliceOver p)).apply_symm_apply c

variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 二つの標準四角形は同じ cospan を持つ。 -/
lemma cofiberFiberComparison_cospan (f : A ⟶ B) (g : A ⟶ C) :
    pullbackCospan (standardFiberSquare (pushoutInclusionB f g) (pushoutInclusionC f g)) =
      pullbackCospan (standardCofiberSquare f g) := by
  apply SSet.horn₂₂.isPushout.hom_ext
  · simp only [pullbackCospan, ← Category.assoc]
    rw [cospanSquareBoundary_rightEdge,
      standardFiberSquare_right, standardCofiberSquare_right]
  · simp only [pullbackCospan, ← Category.assoc]
    rw [cospanSquareBoundary_topEdge,
      standardFiberSquare_top, standardCofiberSquare_top]

/-- 元の cofiber 錐を標準 fiber の cospan 上で読む。 -/
def cofiberFiberSourceCone (f : A ⟶ B) (g : A ⟶ C) :
    JoinCone (pullbackCospan
      (standardFiberSquare (pushoutInclusionB f g) (pushoutInclusionC f g))) :=
  rebaseCone (cofiberFiberComparison_cospan f g) (pullbackCone (standardCofiberSquare f g))

/-- 比較 join 写像は cospan を固定する。 -/
lemma cofiberFiberComparisonJoin_fixed (f : A ⟶ B) (g : A ⟶ C) :
    joinInr (Δ[1] : SSet.{u + 1}) (SSet.horn 2 2) ≫ cofiberFiberComparisonJoin f g =
      pullbackCospan (standardFiberSquare (pushoutInclusionB f g) (pushoutInclusionC f g)) := by
  calc
    _ = (joinInr (Δ[0] : SSet.{u + 1}) (SSet.horn 2 2) ≫
        joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet.{u + 1}))) ≫
        cofiberFiberComparisonJoin f g := by
      rw [joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, cofiberFiberComparisonJoin_face_zero]
      exact (standardFiberCone _ _).property

/-- 元の錐から標準 fiber 錐への、明示的な slice 比較辺。 -/
def cofiberFiberComparisonSliceEdge (f : A ⟶ B) (g : A ⟶ C) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (sliceOver (pullbackCospan
      (standardFiberSquare (pushoutInclusionB f g) (pushoutInclusionC f g)))))
      (cofiberFiberSourceCone f g)
      (standardFiberCone (pushoutInclusionB f g) (pushoutInclusionC f g)) where
  edge := SSet.yonedaEquiv
    (sliceOverCurry (cofiberFiberComparisonJoin f g) (cofiberFiberComparisonJoin_fixed f g))
  src_eq := sliceOverCurry_vertex_of_join _ _ 1 _ (cofiberFiberComparisonJoin_face_one f g)
  tgt_eq := sliceOverCurry_vertex_of_join _ _ 0 _ (cofiberFiberComparisonJoin_face_zero f g)

end SerrePositivity.InfinityCategories
