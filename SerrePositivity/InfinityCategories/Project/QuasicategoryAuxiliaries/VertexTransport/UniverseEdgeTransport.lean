module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.CategoryTheory.Types.Basic

/-!
概要：実辺と合成三角形の宇宙移送、および可逆性の保存・反映。
方針：各次数の ULift を上げ下げし、ホモトピー圏の普遍性で関手を作る。
規約：quasicategory 性は不要。Stable の準重複を新名で軽い入口に置く。
使われ方：局所化の宇宙持ち上げと降下。第 I 段終了時に R が旧入口を付け替える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable {X : SSet.{u}}
/-- 元の辺とその両端点を持ち上げる。 -/
def up {x y : X _⦋0⦌} (e : Truncated.Edge (X := (truncation 2).obj X) x y) :
    Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X))
      (ULift.up x) (ULift.up y) where
  edge := ULift.up e.edge
  src_eq := congrArg ULift.up e.src_eq
  tgt_eq := congrArg ULift.up e.tgt_eq

/-- 持ち上げた辺をその元の両端点へ戻す。 -/
def down {x y : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X)) x y) :
    Truncated.Edge (X := (truncation 2).obj X) x.down y.down where
  edge := e.edge.down
  src_eq := congrArg ULift.down e.src_eq
  tgt_eq := congrArg ULift.down e.tgt_eq

/-- 元の三辺を保って合成三角形を持ち上げる。 -/
def upComp {x y z : X _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj X) x y}
    {f : Truncated.Edge (X := (truncation 2).obj X) y z}
    {g : Truncated.Edge (X := (truncation 2).obj X) x z} (t : Truncated.Edge.CompStruct e f g) :
    Truncated.Edge.CompStruct (up.{u, v} e) (up f) (up g) where
  simplex := ULift.up t.simplex
  d₂ := congrArg ULift.up t.d₂
  d₀ := congrArg ULift.up t.d₀
  d₁ := congrArg ULift.up t.d₁

/-- 同じ合成三角形を元の宇宙へ戻す。 -/
def downComp {x y z : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X)) x y}
    {f : Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X)) y z}
    {g : Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X)) x z}
    (t : Truncated.Edge.CompStruct e f g) :
    Truncated.Edge.CompStruct (down e) (down f) (down g) where
  simplex := t.simplex.down
  d₂ := congrArg ULift.down t.d₂
  d₀ := congrArg ULift.down t.d₀
  d₁ := congrArg ULift.down t.d₁

/-- 辺と三角形の持ち上げがホモトピー圏に誘導する関手。 -/
def upFunctor (X : SSet.{u}) : X.HomotopyCategory ⥤
    (SSet.uliftFunctor.{v, u}.obj X).HomotopyCategory :=
  Truncated.HomotopyCategory.lift (fun x ↦ Truncated.HomotopyCategory.mk (ULift.up x))
    (fun e ↦ Truncated.HomotopyCategory.homMk (up e))
    (fun _ ↦ Truncated.HomotopyCategory.homMk_id _)
    (fun t ↦ Truncated.HomotopyCategory.homMk_comp_homMk (upComp t))

/-- 辺と三角形の降下がホモトピー圏に誘導する関手。 -/
def downFunctor (X : SSet.{u}) : (SSet.uliftFunctor.{v, u}.obj X).HomotopyCategory ⥤
    X.HomotopyCategory :=
  Truncated.HomotopyCategory.lift (fun x ↦ Truncated.HomotopyCategory.mk x.down)
    (fun e ↦ Truncated.HomotopyCategory.homMk (down e))
    (fun _ ↦ Truncated.HomotopyCategory.homMk_id _)
    (fun t ↦ Truncated.HomotopyCategory.homMk_comp_homMk (downComp t))

/-- 可逆性は宇宙の持ち上げで保たれる。 -/
lemma invertible_up {x y : X _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj X) x y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := SSet.uliftFunctor.{v, u}.obj X) (up.{u, v} e) := by
  let := he
  have h := Functor.map_isIso (upFunctor.{u, v} X) (Truncated.HomotopyCategory.homMk e)
  change IsIso (𝟙 _ ≫ Truncated.HomotopyCategory.homMk (up e)) at h
  simpa only [Category.id_comp] using h

/-- 可逆性は元の宇宙へ降下する。 -/
lemma invertible_down {x y : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj (SSet.uliftFunctor.{v, u}.obj X)) x y}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := X) (down e) := by
  let := he
  have h := Functor.map_isIso (downFunctor.{u, v} X) (Truncated.HomotopyCategory.homMk e)
  change IsIso (𝟙 _ ≫ Truncated.HomotopyCategory.homMk (down e)) at h
  simpa only [Category.id_comp] using h
end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
