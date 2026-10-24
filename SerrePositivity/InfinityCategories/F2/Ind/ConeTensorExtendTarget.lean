module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorTargetCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorExtension
public import SerrePositivity.InfinityCategories.F1.Universe.CoconeShapeNaturality

/-!
概要：元の補間領域の余錐から得た全拡張は、同じ元の終点面の余錐を厳密に回収する。
方針：元の逆比較の終点面と、同じ余錐形状の宇宙自然性を合成する。
規約：元の全族・指定包含・全余錐を保持する。
使われ方：指定評価下の共同余錐を、元の全終点拡張の同じ面へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ全拡張の元の終点面は、元の補間領域への指定包含の全余錐。
方針：元の比較同型と宇宙自然性。規約：全射の等号。使われ方：指定変換を保つ全拡張。 -/
lemma coneTensorExtend_target {A L : SSet.{u}} {X : SSet.{max u v}}
    {H : (SSet.uliftFunctor.{v, u}).obj (coneTensorCorner A L) ⟶ X} (c : JoinCocone H) :
    (SSet.uliftFunctor.{v, u}).map
      (tensorRightPoint (join A (Δ[0] : SSet.{u})) (joinInr L Δ[0])) ≫ coneTensorExtend c =
    (uliftCoconeShapeIso.{u, v} A 0).hom ≫
      joinMap ((SSet.uliftFunctor.{v, u}).map (coneTensorTargetInclusion A L))
        (𝟙 (Δ[0] : SSet.{max u v})) ≫ c.val := by
  rw [coneTensorExtend, ← Category.assoc, ← Functor.map_comp, coneTensorCoconeIso_inv_target]
  have h := congrArg (fun f ↦ f ≫ c.val)
    (uliftCoconeShapeIso_hom_naturality (coneTensorTargetInclusion A L) 0)
  simpa only [Category.assoc] using h
end SerrePositivity.InfinityCategories.F2.Ind
