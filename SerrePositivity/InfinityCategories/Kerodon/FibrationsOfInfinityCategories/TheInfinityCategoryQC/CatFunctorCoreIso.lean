module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.QuasicategoryCore

/-!
概要：関手同型と関手 core の頂点同型、連結成分の一致の接続。
方針：同型の辺を core に持ち上げ、Kan 複体の連結成分の同値関係を同型へ送る。
規約：宇宙を持ち上げた core の連結成分は元の宇宙へ読み戻せる。
使われ方：Cat_∞ の辺の類の一致から実際の関手同型を回収する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：関手同型は QCat の豊穣 Hom の二頂点間の同型を与える。
方針：可逆自然変換を core の辺にし、そのホモトピー圏の射を同型にする。
規約：元の指定関手 f、g に対応する零単体を端点とする。
使われ方：関手の同値の逆条件を Cat_∞ の辺の逆条件へ送る。 -/
def catInfinityFunctorCoreVertexIso {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} {f g : X ⟶ Y} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (SimplicialCategory.homEquiv' X Y f) (SimplicialCategory.homEquiv' X Y g) := by
  let e : SSet.Edge (X := SimplicialCategory.sHom X Y)
      (SimplicialCategory.homEquiv' X Y f) (SimplicialCategory.homEquiv' X Y g) :=
    { edge := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge h).edge, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible h))⟩
      src_eq := by apply Subtype.ext; exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge h).src_eq
      tgt_eq := by apply Subtype.ext; exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge h).tgt_eq }
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (SimplicialCategory.sHom X Y)) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

/-- 概要：単体の宇宙の持ち上げは連結成分を元の宇宙へ読み戻せる。
方針：零単体の ULift.down と、辺の ULift.down を商へ降ろす。
規約：単体集合間の宇宙の異なる射を仮定せず、連結成分の間の関数を作る。
使われ方：Cat_∞ の写像空間比較から元の小さい core の連結成分へ戻す。 -/
def coherentUliftPiZeroDown (X : SSet.{u}) :
    SSet.π₀ ((SSet.uliftFunctor.{v, u}).obj X) → SSet.π₀ X :=
  SSet.π₀.lift (fun x ↦ SSet.π₀.mk x.down) (by
    intro x y e
    exact SSet.π₀.sound
      { edge := e.edge.down
        src_eq := congrArg ULift.down e.src_eq
        tgt_eq := congrArg ULift.down e.tgt_eq })

/-- 概要：Kan 複体の同じ連結成分の頂点はホモトピー圏で同型。
方針：辺の生成する同値関係に帰納し、亜群の射と同型の対称・合成を使う。
規約：非空な同型を返し、標準の辺や経路の選択は要求しない。
使われ方：関手 core の連結成分の等式から関手同型を復元する。 -/
lemma coherentVertexIso_of_piZero_eq {X : SSet.{u}} [KanComplex X] {x y : X _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  have hh := (SSet.π₀.mk_eq_mk_iff x y).mp h
  clear h
  induction hh with
  | rel x y h =>
    obtain ⟨e⟩ := h
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) :=
      IsGroupoid.all_isIso (C := hoFunctor.obj X) _
    exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)⟩
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih => exact ⟨(Classical.choice ih).symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨Classical.choice ih₁ ≪≫ Classical.choice ih₂⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
