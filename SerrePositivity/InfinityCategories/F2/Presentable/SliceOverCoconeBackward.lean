module

public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverCoconeForward

/-!
概要：底の余錐圏の増大余錐上の slice から対象上の元の余錐圏へ戻す。
方針：二回の uncurry を順方向の join 結合同型で組み替えて戻す。
規約：元の対象への全増大図式を固定する。
使われ方：二重 slice の全同型と対象上の余極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {K X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x)

/-- 概要：底の元の増大余錐の頂点は元の対象の頂点。
方針：uncurry の右固定条件を読む。
規約：元の点射を保持する。
使われ方：逆比較の対象上の固定条件。 -/
lemma sliceOverAugmentationCocone_vertex :
    (sliceUnderProjection (a ≫ sliceOverProjection x)).app (Opposite.op ⦋0⦌)
      (sliceOverAugmentationCocone x a) = SSet.yonedaEquiv x := by
  change (show JoinCocone (a ≫ sliceOverProjection x) from
    sliceOverAugmentationCocone x a).vertex = _
  rw [JoinCocone.vertex_eq]
  exact congrArg SSet.yonedaEquiv (sliceOverUncurry_fixed a)

/-- 概要：元の増大余錐上の普遍射を二重 join の順方向で組み替える。
方針：二回 uncurry して結合同型で前合成する。
規約：パラメーターは slice 全体。
使われ方：対象上の余錐圏への逆比較。 -/
def sliceOverCoconeBackwardDiagram :
    join (join K (sliceOver (SSet.yonedaEquiv.symm
      (sliceOverAugmentationCocone x a)))) Δ[0] ⟶ X :=
  (stableJoinAssociator K _ Δ[0]).hom ≫
    sliceUnderUncurry (sliceOverUncurry (𝟙 (sliceOver
      (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a)))))

/-- 概要：逆向きの組み替えは元の対象を固定する。
方針：右包含、二つの uncurry 射影・固定則と元の余錐頂点を使う。
規約：元の点射の等式。
使われ方：対象上への curry の固定条件。 -/
lemma sliceOverCoconeBackwardDiagram_fixed :
    joinInr (join K (sliceOver (SSet.yonedaEquiv.symm
      (sliceOverAugmentationCocone x a)))) Δ[0] ≫ sliceOverCoconeBackwardDiagram x a = x := by
  rw [sliceOverCoconeBackwardDiagram, ← Category.assoc, stableJoinAssociator_inr,
    Category.assoc, sliceUnderUncurry_projection, ← Category.assoc,
    sliceOverUncurry_fixed, SSet.yonedaEquiv_symm_comp, sliceOverAugmentationCocone_vertex,
    Equiv.symm_apply_apply]

/-- 概要：逆向きの組み替えは元の対象上の図式へ制限される。
方針：中間包含と二つの uncurry の固定条件を使う。
規約：元の全図式を厳密に回収する。
使われ方：元の余錐圏への curry の固定条件。 -/
lemma sliceOverCoconeBackwardDiagram_left :
    joinMap (joinInl K (sliceOver (SSet.yonedaEquiv.symm
      (sliceOverAugmentationCocone x a)))) (𝟙 (Δ[0] : SSet.{u})) ≫
      sliceOverCoconeBackwardDiagram x a = sliceOverUncurry a := by
  rw [sliceOverCoconeBackwardDiagram, ← Category.assoc, stableJoinAssociator_middle,
    ← sliceUnderUncurry_precomp, sliceOverUncurry_fixed, sliceUnderUncurry_yoneda]
  rfl

/-- 概要：底の元の増大余錐上の slice から元の対象上の余錐圏への逆比較。
方針：組み替えた全射を二回 curry する。
規約：元の対象への図式を保持する。
使われ方：二重 slice 比較の逆射。 -/
def sliceOverCoconeBackward :
    sliceOver (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a)) ⟶ sliceUnder a :=
  sliceUnderCurry
    (sliceOverCurry (sliceOverCoconeBackwardDiagram x a)
      (sliceOverCoconeBackwardDiagram_fixed x a)) (by
        apply sliceOverUncurry_injective x
        rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
        exact sliceOverCoconeBackwardDiagram_left x a)

/-- 概要：逆比較の二回の uncurry は組み替えた普遍全射。
方針：二つの curry の逆則を使う。
規約：全パラメーターの等式。
使われ方：両比較の合成の厳密な計算。 -/
lemma sliceOverCoconeBackward_uncurry :
    sliceOverUncurry (sliceUnderUncurry (sliceOverCoconeBackward x a)) =
      sliceOverCoconeBackwardDiagram x a := by
  rw [sliceOverCoconeBackward, sliceUnderUncurry_curry, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.F2.Presentable
