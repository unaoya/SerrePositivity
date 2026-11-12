module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：全頂点を含む部分図式上で固定した関手の fiber と区間模型の Kan 性。
方針：制限の fiber の辺を全頂点で評価すると恒等辺になることを使う。
規約：標的は quasicategory でよく、Kan 性を仮定しない。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、両端固定の区間模型の Kan 性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：前合成した関手の頂点での評価は像の頂点での評価。
方針：関手単体の評価で自然変換の定値単体への作用を計算する。
規約：始域と標的の quasicategory 性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§4.6.6（Tag 04HY）、制限した関手の点ごとの比較。 -/
lemma evaluateFunctorAt_pre {A B X : SSet.{u}} (j : A ⟶ B) (a : A _⦋0⦌) :
    (pre j).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (j.app (Opposite.op ⦋0⦌) a) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  change F.app d (𝟙 d) (j.app d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len)) =
    F.app d (𝟙 d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (j.app (Opposite.op ⦋0⦌) a) d.unop.len)
  congr 1
  exact ConcreteCategory.congr_hom (C := Type u)
    (j.naturality (SimplexCategory.const d.unop ⦋0⦌ 0).op) a

/-- 概要：全頂点を含む部分図式上の固定 fiber 内の全ての辺は可逆。
方針：包含で写した関手の辺を全頂点で評価し、固定図式上では恒等辺となることを使う。
規約：j は単射で、零次成分が全射である。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、固定端点の写像空間の亜群性。 -/
lemma isInvertibleEdge_preFiber_of_vertexSurjective {A B X : SSet.{u}}
    [Quasicategory X] (j : A ⟶ B) [Mono j]
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    (p : ((ihom A).obj X) _⦋0⦌)
    {s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) p) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) p)) s t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_vertexFiber_iff ((pre j).app X) p e).mpr
  rcases s with ⟨s, hs⟩
  rcases t with ⟨t, ht⟩
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).surjective s
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).surjective t
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom B).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) := e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre j).app X) p))
  have hid : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) p) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom A).obj X)) p))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hrest : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e'.map ((truncation 2).map ((pre j).app X))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e.edge.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one p))).mpr hid
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e').mpr
  intro b
  obtain ⟨a, rfl⟩ := hj b
  have hm := hrest.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)
  have he :
      ((e'.map ((truncation 2).map ((pre j).app X))).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))).edge =
      (e'.map ((truncation 2).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (j.app (Opposite.op ⦋0⦌) a)))).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a).app (Opposite.op ⦋1⦌)
      (((pre j).app X).app (Opposite.op ⦋1⦌) e'.edge) = _
    have hn := NatTrans.congr_app (evaluateFunctorAt_pre (X := X) j a) (Opposite.op ⦋1⦌)
    exact congrArg (fun (k : ((ihom B).obj X) _⦋1⦌ ⟶ X _⦋1⦌) ↦ k e'.edge) hn
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mp hm

/-- 概要：全頂点を含む単射への関手の制限の各固定 fiber は Kan 複体。
方針：制限が inner fibration であることと全辺の可逆性からホモトピー圏の亜群性を得る。
規約：図式の対象集合を固定する条件であり、元の図式の辺は任意。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、区間模型の全ホーン充填。 -/
@[kerodon 01P1]
lemma kanComplex_preFiber_of_vertexSurjective {A B X : SSet.{u}} [Quasicategory X]
    (j : A ⟶ B) [Mono j] (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    (p : ((ihom A).obj X) _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) p) := by
  have hg : IsGroupoid (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) p)) := by
    constructor
    intro a b f
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre j).app X) p) a b f
    exact isInvertibleEdge_preFiber_of_vertexSurjective j hj p e
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid _

/-- 概要：quasicategory の両端固定の区間写像空間は Kan 複体。
方針：区間の境界が区間の全ての頂点を含むことを一般の固定 fiber の補題に適用する。
規約：元の X の Kan 性は要求しない。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、左右の pinched 模型の共通比較先。 -/
@[kerodon 01JC]
instance intervalMappingSpace_kanComplex {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) := by
  apply kanComplex_preFiber_of_vertexSurjective (boundary 1).ι
  intro v
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  exact ⟨⟨stdSimplex.obj₀Equiv.symm i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 i⟩, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
