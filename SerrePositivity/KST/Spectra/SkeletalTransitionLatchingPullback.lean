module

public import SerrePositivity.KST.Spectra.SkeletalStandardLatching
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.SkeletonTransitionPullback
public import SerrePositivity.KST.Spectra.TypesColimitPullback

/-!
概要：標準単体の骨格間の包含の latching 正方形は各単体次数で pullback。
方針：各固有面での骨格の逆像を使い、標的の latching 余極限の代表から交わりを回収する。
規約：有限骨格の実際の latching 射と包含を比較する。
使われ方：Goerss–Jardine VIII §1。部分 Tot の遷移の Reedy 単射性。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.SkeletalStandardLatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev diagram (n : ℕ) : CosimplicialObject SSet.{u} :=
  stdSimplex ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.functor n

abbrev transition {n m : ℕ} (h : n ≤ m) : diagram.{u} n ⟶ diagram.{u} m :=
  Functor.whiskerLeft stdSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.transition h)

/-- 骨格間の包含に対する latching の自然性正方形は次数ごとの pullback。 -/
lemma transition_latching_app_isPullback {n m : ℕ} (h : n ≤ m)
    (j : SimplexCategory) (k : SimplexCategoryᵒᵖ) :
    IsPullback (((latchingEvaluation simplex j).map (transition.{u} h)).app k)
      (((latchingComparison simplex j).app (diagram.{u} n)).app k)
      (((latchingComparison simplex j).app (diagram.{u} m)).app k)
      (((transition.{u} h).app j).app k) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type u)).obj k
  let c := E.mapCocone (colimit.cocone (latchingSource simplex j ⋙ diagram.{u} n))
  let d := E.mapCocone (colimit.cocone (latchingSource simplex j ⋙ diagram.{u} m))
  let θ := transition.{u} h
  let α := Functor.whiskerRight (Functor.whiskerLeft (latchingSource simplex j) θ) E
  let : Mono ((latchingComparison simplex j).app (diagram.{u} n)) := mono n j
  refine TypesColimitPullback.of_components c d
    (isColimitOfPreserves E (colimit.isColimit _)) α _ _ _ _ ?_ ?_ ?_
  · change E.map ((latchingEvaluation simplex j).map θ) ≫
        E.map ((latchingComparison simplex j).app (diagram.{u} m)) =
      E.map ((latchingComparison simplex j).app (diagram.{u} n)) ≫ E.map (θ.app j)
    rw [← E.map_comp, ← E.map_comp]
    exact congrArg (fun f ↦ E.map f) ((latchingComparison simplex j).naturality θ)
  · intro a
    change E.map (colimit.ι (latchingSource simplex j ⋙ diagram.{u} n) a) ≫
        E.map (colim.map (Functor.whiskerLeft (latchingSource simplex j) θ)) =
      E.map (θ.app a.obj.left) ≫
        E.map (colimit.ι (latchingSource simplex j ⋙ diagram.{u} m) a)
    rw [← E.map_comp, ← E.map_comp]
    exact congrArg (fun f ↦ E.map f)
      (colimit.ι_map (Functor.whiskerLeft (latchingSource simplex j) θ) a)
  · intro a
    have hF : c.ι.app a ≫ E.map ((latchingComparison simplex j).app (diagram.{u} n)) =
        E.map ((diagram.{u} n).map a.obj.hom) := by
      change E.map (colimit.ι _ a) ≫ E.map (colimit.desc _ _) = _
      rw [← E.map_comp, colimit.ι_desc]
    have hG : d.ι.app a ≫ E.map ((latchingComparison simplex j).app (diagram.{u} m)) =
        E.map ((diagram.{u} m).map a.obj.hom) := by
      change E.map (colimit.ι _ a) ≫ E.map (colimit.desc _ _) = _
      rw [← E.map_comp, colimit.ι_desc]
    change IsPullback (E.map (θ.app a.obj.left))
      (c.ι.app a ≫ E.map ((latchingComparison simplex j).app (diagram.{u} n)))
      (d.ι.app a ≫ E.map ((latchingComparison simplex j).app (diagram.{u} m))) (E.map (θ.app j))
    rw [hF, hG]
    let : Mono a.obj.hom := a.property.1
    let : Mono (stdSimplex.{u}.map a.obj.hom) := standard_map_mono a.obj.hom
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.transition_app_isPullback (stdSimplex.map a.obj.hom) h k

end
end SerrePositivity.KST.Spectra.SkeletalStandardLatching
