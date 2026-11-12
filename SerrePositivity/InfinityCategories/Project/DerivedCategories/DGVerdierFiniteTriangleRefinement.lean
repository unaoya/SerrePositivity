module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierRefinedThreeSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornFiniteFillers

/-! # 実二単体有限族の追加閉分母と実分母 over 三単体

概要：同じ頂点錐の指定二単体有限族へ、一つの追加実閉分母後の全実三単体を供給する。
方針：有限四次ホーンの同時充填を、そのまま実分母 over へ回収する。
規約：空族も含む。使われ方：有限二次図式の共通錐の組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [Small.{u} D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) {m : ℕ}
variable (τ : Fin m → K _⦋2⦌)
variable (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i (τ j))))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i (τ j)))))

/-- 指定実二単体有限族の、一つの追加実閉分母による同時残差・充填データ。 -/
abbrev DGVerdierFiniteTriangleRefinement :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornFiniteRefinement P
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) C.denominator.obj.left)
    (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C (τ j) (G j))

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (T : DGVerdierFiniteTriangleRefinement A D C τ G)

/-- 同じ追加閉分母後の各実二単体に付随する、実分母部分圏内の実三単体。 -/
def DGVerdierFiniteTriangleRefinement.simplex (j : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋3⦌ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeSimplex A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator
    (T.filler j) (T.filler_fac j)

/-- 有限族の全実三単体の零面は、それぞれ元の指定実二単体そのもの。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_face0 (j : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ 0
      (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j) = f.app _ (τ j) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedThreeSimplex_face0 A D C (τ j) (G j)
    (T.residuals j).q (T.residuals j).s (T.residuals j).denominator
    (T.filler j) (T.filler_fac j)

/-- 実三単体の台は、供給した同じ実四次充填の over 回収そのもの。 -/
lemma DGVerdierFiniteTriangleRefinement.simplex_val (j : Fin m) :
    (DGVerdierFiniteTriangleRefinement.simplex A D C τ G T j).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C (τ j) (G j)
        (T.residuals j).q (T.residuals j).s (T.filler j) (T.filler_fac j) := rfl

/-- 任意の指定実二単体有限族に、同時実三単体を持つ追加閉分母データがある。 -/
theorem dgVerdierFiniteTriangleRefinement_nonempty :
    Nonempty (DGVerdierFiniteTriangleRefinement A D C τ G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTrianglesResidualRefinement_nonempty A D C τ G

end SerrePositivity.InfinityCategories.Project.DerivedCategories
