module

public import SerrePositivity.KST.Spectra.D3StageLoopStructureFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoWhiskerCancellation

/-!
概要：全図式に写した指定同型を頂点で評価し、元の同型の同じ前合成へ戻す。
方針：実後合成と頂点評価の全単体の厳密交換を、同じホモトピー圏の射へ移す。
規約：同型の存在でなく指定値を保持する。始域・図式形状は任意。
使われ方：実 loop 構造同型の四角の成分と元の BF 構造射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 元の全後合成を頂点で評価しても、同じ頂点評価への前合成そのもの。 -/
lemma d3FunctorPostcomposition_evaluate {K X Y : SSet.{u}} (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y ≫
      (ihom ((ihom K).obj X)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k) =
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).app Y := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro G
  rfl


/-- 元の後合成同型の端点正規化は、写した同じ頂点同型の値を保持する。 -/
lemma d3FunctorIsoMapPost_heq {K X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    HEq (e.map_post K) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.map_post
  exact (cast_heq _ _).trans (cast_heq _ _)


/-- 端点の等式を明示すれば、同じ同型の値の保持は関手による像でも保たれる。 -/
lemma d3MapIso_heq {C : Type v} {D : Type w} [Category C] [Category D]
    (F : C ⥤ D) {a b a' b' : C} {e : a ≅ b} {e' : a' ≅ b'}
    (ha : a = a') (hb : b = b') (h : HEq e e') : HEq (F.mapIso e) (F.mapIso e') := by
  subst a' b'
  cases h
  rfl

/-- 全図式へ写した同じ指定同型の頂点評価は、元の同型への前合成そのもの。 -/
lemma d3FunctorIsoMapPost_evaluate {K X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (k : K _⦋0⦌) :
    HEq ((e.map_post K).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k))
      (e.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)) := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap K X Y
  let q := (ihom ((ihom K).obj X)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k)
  let Q := SSet.mapHomotopyCategory q
  have hm := d3MapIso_heq Q
    (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap_vertex (K := K) f).symm)
    (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPostcompositionMap_vertex (K := K) g).symm)
    (d3FunctorIsoMapPost_heq (K := K) e)
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp e P q
  have hn := congrArg SSet.mapHomotopyCategory
    (d3FunctorPostcomposition_evaluate (X := X) (Y := Y) k)
  have he := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq hn e
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_eq_mapIso]
  exact hm.trans ((heq_of_eq hc).trans he)


/-- 同じ全図式の指定値を任意の元の族へ制限しても、頂点で元の同型を回収する。 -/
lemma d3FunctorIsoMapPost_evaluate_precomp {A K X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (k : K _⦋0⦌) (r : A ⟶ (ihom K).obj X) :
    HEq (((e.map_post K).precomp r).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k))
      (e.precomp (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq
    (e.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))
    ((e.map_post K).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Y) k)) rfl rfl
    (d3FunctorIsoMapPost_evaluate e k) r
  exact h.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e _ r))

end SerrePositivity.KST.Spectra
