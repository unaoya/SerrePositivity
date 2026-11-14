module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapComposition

/-!
概要：自由 Hom の生成辺への全 pinched 係数の包含と評価を公開する。
方針：生成辺と Hom 鎖写像の合成則を使う。
規約：Small 仮定と閉前合成鎖写像の構成には依存しない。
使われ方：一般対象宇宙の係数 prism の全単体比較の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (A : Type u) [CommRing A]

/-- 元の Hom の全次数の単体を、自由係数 dg 圏の指定 Hom に含める。 -/
def dgWalkingHomPinched (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (q y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A (homObject A D q y))

/-- dg 関手の Hom 鎖写像は、全単体の元の dg nerve の像を保つ。 -/
lemma dgFunctorPinchedChainMap_val {C D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D) {x y : C} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A C x y).obj (Opposite.op ⟨n⟩)) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map x y)).app (Opposite.op ⟨n⟩) s).val = s.val.map F := by
  have h := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_pinchedHomMap_eq F x y)
  exact h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso_hom_val _ _ _)

/-- 自由係数を任意の Hom 鎖写像で評価すると、その鎖写像の全 pinched 作用を回収する。 -/
lemma dgWalkingHomPinched_evaluation (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
    (q y : D) (q' y' : E) (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D q y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E q' y') :
    dgWalkingHomPinched A D q y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ := by
  rw [dgWalkingHomPinched, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator]

/-- 恒等評価は、元の pinched Hom 全体の恒等射を回収する。 -/
lemma dgWalkingHomPinched_identity (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (q y : D) :
    dgWalkingHomPinched A D q y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomSource A (homObject A D q y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomTarget A (homObject A D q y))) = 𝟙 _ := by
  rw [dgWalkingHomPinched_evaluation, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id]

/-- 自由係数単体の評価は、元の係数鎖写像による全単体の像そのもの。 -/
lemma dgWalkingHomPinched_evaluation_val (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
    (q y : D) (q' y' : E) (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D q y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E q' y') {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y).obj (Opposite.op ⟨n⟩)) :
    ((dgWalkingHomPinched A D q y).app (Opposite.op ⟨n⟩) s).val.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ) =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ).app (Opposite.op ⟨n⟩) s).val := by
  have h := congrArg (fun f => (f.app (Opposite.op ⟨n⟩) s).val)
    (dgWalkingHomPinched_evaluation A D E q y q' y' φ)
  exact (dgFunctorPinchedChainMap_val A
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) q' y' φ)
      ((dgWalkingHomPinched A D q y).app (Opposite.op ⟨n⟩) s)).symm.trans h

end SerrePositivity.InfinityCategories.Project.DerivedCategories
