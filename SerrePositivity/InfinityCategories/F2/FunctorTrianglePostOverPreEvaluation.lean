module

public import SerrePositivity.InfinityCategories.F2.RelativeFunctorPostIsoOverPreEvaluation
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleSequentialPostComparison
public import SerrePositivity.InfinityCategories.F2.FunctorTriangleRelativeComparison

/-!
概要：元の三角形比較の sequential な指定成分は、底上の前合成に対して自然。
方針：同じ元の相対三角形比較の豊穣後合成の自然性へ戻し、標的表示の補正を保持する。
規約：指定値と端点等式を保持。使われ方：三つの全選択族の関係を元の全空間へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C D : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c) (p : C ⟶ B) (d : D ⟶ B)
  (t : D ⟶ C) (ht : t ≫ p = d)
local notation "va" => leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)
local notation "vb" => leftUnstraighteningMappingVertexMap G J (coherentVertexOfHomotopy b)
local notation "vc" => leftUnstraighteningMappingVertexMap F J (coherentVertexOfHomotopy c)
local notation "q" => leftUnstraighteningProjection F
local notation "r" => leftUnstraighteningProjection J
local notation "R₀" => relativeFunctorOverPre q
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
local notation "R₂" => relativeFunctorOverPre r
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)

/-- 元の三角形の指定成分を底上の射で制限しても、同じ sequential 比較の指定値を保持。 -/
lemma functorTriangleSequentialPostComparison_overPre_app_heq
    (x : (relativeFunctorSpace q p) _⦋0⦌) :
    HEq (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x) R₂)
      ((functorTriangleSequentialPostComparison T d).app ((R₀).app _ x)) := by
  have hc : ((va).val ≫ (vb).val) ≫ r = q := by
    rw [Category.assoc, (vb).property, (va).property]
  have h := relativeFunctorPostVertexIso_overPre_app_heq p d q r t ht (vc).val
    ((va).val ≫ (vb).val) (vc).property hc (functorTriangleRelativeComparison T) x
  change HEq (VertexIso.map ((functorTrianglePostComparison T p).app x) R₂)
    ((functorTrianglePostComparison T d).app ((R₀).app _ x)) at h
  have he := functorTriangleSequentialPostComparison_app_heq_post T p x
  have hp := relativeFunctorPost_comp (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) (leftUnstraighteningProjection J)
    (va).val (va).property (vb).val (vb).property p
  have hm := vertexIso_map_heq_of_heq ((functorTriangleSequentialPostComparison T p).app x)
    ((functorTrianglePostComparison T p).app x) rfl
    (congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) hp) he R₂
  exact hm.trans (h.trans
    (functorTriangleSequentialPostComparison_app_heq_post T d ((R₀).app _ x)).symm)

end SerrePositivity.InfinityCategories.F2
