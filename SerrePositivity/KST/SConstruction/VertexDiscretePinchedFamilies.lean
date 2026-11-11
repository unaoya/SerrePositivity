module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.VertexDiscreteFunctionSimplices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-! # 離散頂点上の固定端点写像空間の族
概要：各頂点で指定した固定端点の高次単体・辺を一つの関手空間の単体・辺へ束ねる。
方針：離散頂点上の関手単体の座標表示を pinched 条件へ制限する。
規約：固定された始点・終点を全次数で保つ。
使われ方：対象ごとの構造射との成分一致を、離散部分上の一つの等式にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 離散頂点ごとの固定端点の単体を、関手空間の固定端点の単体へ束ねる。 -/
def vertexDiscretePinchedSimplex {A X : SSet.{u}}
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌) {n : ℕ}
    (s : ∀ a : A _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) f)
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) g)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g) _⦋n⦌ where
  val := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => (s a).val)
  source := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map]
    have he : (fun a => X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n).op (s a).val) =
        (fun a => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant f n)) := by
      funext a
      exact (s a).source.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f n).symm
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex he).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct _)
  target := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map]
    have he : (fun a => X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op (s a).val) =
        (fun a => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) g) := by
      funext a
      exact (s a).target
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex he).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct g)

/-- 固定端点の単体の座標表示は全ての面・退化に整合する。 -/
lemma vertexDiscretePinchedSimplex_map {A X : SSet.{u}}
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ∀ a : A _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) f)
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) g)) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g).map α.op (vertexDiscretePinchedSimplex f g s) =
      vertexDiscretePinchedSimplex f g (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) f)
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) g)).map α.op (s a)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) _

/-- 関手空間の固定端点の単体は、その全ての座標の像から厳密に復元できる。 -/
lemma vertexDiscretePinchedSimplex_reconstruct {A X : SSet.{u}}
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌) {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g) _⦋n⦌) :
    vertexDiscretePinchedSimplex f g
      (fun a => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f g).app (Opposite.op ⦋n⦌) s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct s.val

/-- 全ての座標で指定した辺を保つ、関手空間の固定端点の辺が存在する。 -/
lemma vertexDiscretePinched_nonempty_edge {A X : SSet.{u}}
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌) {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g) _⦋0⦌}
    (h : ∀ a : A _⦋0⦌, Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) f)
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) g)).Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f g).app (Opposite.op ⦋0⦌) v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f g).app (Opposite.op ⦋0⦌) w))) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g).Edge v w) := by
  let γ (a : A _⦋0⦌) := Classical.choice (h a)
  refine ⟨SSet.Edge.mk (vertexDiscretePinchedSimplex f g (fun a => (γ a).edge)) ?_ ?_⟩
  · have hm := vertexDiscretePinchedSimplex_map f g (SimplexCategory.δ (1 : Fin 2)) (fun a => (γ a).edge)
    exact hm.trans ((congrArg (vertexDiscretePinchedSimplex f g) (funext (fun a => (γ a).src_eq))).trans
      (vertexDiscretePinchedSimplex_reconstruct f g v))
  · have hm := vertexDiscretePinchedSimplex_map f g (SimplexCategory.δ (0 : Fin 2)) (fun a => (γ a).edge)
    exact hm.trans ((congrArg (vertexDiscretePinchedSimplex f g) (funext (fun a => (γ a).tgt_eq))).trans
      (vertexDiscretePinchedSimplex_reconstruct f g w))

/-- 離散頂点上の固定端点の写像の成分は、全ての座標の成分で検出できる。 -/
lemma vertexDiscretePinched_piZero_injective {A X : SSet.{u}} [Quasicategory X]
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌) {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom f g) _⦋0⦌}
    (h : ∀ a : A _⦋0⦌, SSet.π₀.mk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f g).app (Opposite.op ⦋0⦌) v) =
        SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) f g).app (Opposite.op ⦋0⦌) w)) :
    SSet.π₀.mk v = SSet.π₀.mk w := by
  obtain ⟨e⟩ := vertexDiscretePinched_nonempty_edge f g (fun a => by
    obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq (h a)
    obtain ⟨γ, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ e.hom
    exact ⟨SSet.Edge.ofTruncated γ⟩)
  exact SSet.π₀.sound e

end SerrePositivity.KST.SConstruction
