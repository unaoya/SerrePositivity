module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.FullColimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullPullbackReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullZeroObject

/-! # 四頂点の条件による実 dg 四角形の制限

概要：四頂点が充満 dg 部分圏に属する四角形を全単体ごと持ち上げる。
方針：頂点による包含像の判定と全境界充填の反映を使う。
規約：四角形全体とその普遍性を保持。使われ方：ホモトピー表現可能加群の部分圏。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (P : D → Prop)

/-- 四頂点に対象条件がある実四角形を充満 dg 部分圏内へ制限する。 -/
def dgFullSquareLift (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0)) :
    (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.DifferentialGraded.DGFullSubcategory D P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift A D P F (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := SSet.stdSimplex.obj₀Equiv.symm.surjective b
    exact hP i j)

/-- 部分圏へ制限した実四角形の包含像は元の四角形。 -/
lemma dgFullSquareLift_inclusion (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A D P) = F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp A D P F _

/-- 四頂点の制限は各実頂点の包含像を厳密に保つ。 -/
lemma dgFullSquareLift_vertex_inclusion
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0)) (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A D P)).app _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP) i j) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgFullSquareLift A D P F hP ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) i j = _
  rw [dgFullSquareLift_inclusion]

/-- 零角の実四角形を制限すると零角は保持される。 -/
lemma dgFullSquareLift_zero_corner
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0))
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP) 0 1) := by
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion A D P
    rw [dgFullSquareLift_vertex_inclusion]
    exact hz.1
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion A D P
    rw [dgFullSquareLift_vertex_inclusion]
    exact hz.2

/-- 押し出し四角形の全単体を制限すると部分圏でも押し出し。 -/
lemma dgFullSquareLift_isPushout
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion A D P (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgFullSquareLift A D P F hP ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))
  rw [dgFullSquareLift_inclusion]
  exact hF

/-- 引き戻し四角形の全単体を制限すると部分圏でも引き戻し。 -/
lemma dgFullSquareLift_isPullback
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0))
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isPullbackSquare_of_fullInclusion A D P
  rw [dgFullSquareLift_inclusion]
  exact hF

/-- 制限した実四角形の指定辺は包含の単射性で元の指定辺と同定できる。 -/
lemma dgFullSquareLift_edge
    (F : (Δ[1] ⊗ Δ[1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hP : ∀ i j : Fin 2, P ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F i j).obj 0))
    (δ : (Δ[1] : SSet.{max u v}) ⟶ Δ[1] ⊗ Δ[1])
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.DifferentialGraded.DGFullSubcategory D P)) _⦋0⦌}
    (e : SSet.Truncated.Edge
      (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.DifferentialGraded.DGFullSubcategory D P))) x y)
    (he : δ ≫ F = SSet.yonedaEquiv.symm
      (e.map ((SSet.truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion A D P)))).edge) :
    δ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift A D P F hP = SSet.yonedaEquiv.symm e.edge := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P))).1
  rw [Category.assoc, dgFullSquareLift_inclusion, he, SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
