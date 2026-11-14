module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation

/-! # 自由 dg 関手の評価と後合成

概要：自由 dg 圏からの評価を後合成すると、生成辺を後合成した評価を得る。
方針：生成辺からの再構成と lift の生成辺公式を使う。
規約：対象族を明示する厳密な関手等式。使われ方：自由 Hom prism の商比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (O : Type v) [Small.{u} O]
variable (D : Type w) [DGCategory A D] (E : Type z) [DGCategory A E]

/-- 自由 dg 圏からの評価の後合成は、生成辺の像の後合成から再構成される。 -/
lemma dgFreeLift_postcomp (K : FreeDGCategory.ComplexQuiver A O) (o : O → D)
    (f : ∀ x y, K x y ⟶ homObject A D (o x) (o y)) (Q : DGFunctor A D E) :
    (FreeDGCategory.lift A O D K o f).comp Q =
      FreeDGCategory.lift A O E K (fun x => Q.obj (o x))
        (fun x y => f x y ≫ Q.map (o x) (o y)) := by
  refine (FreeDGCategory.lift_reconstruction A O E K
    ((FreeDGCategory.lift A O D K o f).comp Q)).symm.trans ?_
  congr 1
  funext x y
  change FreeDGCategory.edgeInclusion A O K x y ≫
    ((FreeDGCategory.lift A O D K o f).map x y ≫ Q.map (o x) (o y)) = _
  rw [← Category.assoc, FreeDGCategory.lift_edge]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
