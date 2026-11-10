module

public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体のホモトピー同値と quasicategory の同値の比較。
方針：ホモトピーを関手単体集合の辺にし、Kan 性から可逆性を得る。
規約：モデル構造の弱同値は用いない。
使われ方：Kerodon §4.5.1、Remark 4.8.3.9 の写像空間の同値。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：実際の単体的ホモトピーは関手単体集合の辺を与える。
方針：ホモトピーを curry して一次単体に戻し、両端を計算する。
規約：始点は f、終点は g の関手頂点。
使われ方：Kerodon §4.5.1 の辺とホモトピーの相互変換。 -/
@[kerodon 00TU]
def functorEdgeOfSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (functorVertex f) (functorVertex g) where
  edge := SSet.yonedaEquiv (curry H.h)
  src_eq := by
    change ((ihom X).obj Y).δ 1 (SSet.yonedaEquiv (curry H.h)) = functorVertex f
    rw [← functorVertex_uncurry_zero, Equiv.symm_apply_apply, uncurry_curry, H.h₀]
  tgt_eq := by
    change ((ihom X).obj Y).δ 0 (SSet.yonedaEquiv (curry H.h)) = functorVertex g
    rw [← functorVertex_uncurry_one, Equiv.symm_apply_apply, uncurry_curry, H.h₁]

/-- 概要：Kan 複体を標的とするホモトピーは関手単体集合のホモトピー圏の同型を与える。
方針：内部 Hom の Kan 性によりホモトピーの辺の類を同型にする。
規約：始域の Kan 性は不要。
使われ方：Kerodon §4.5.1、Remark 4.8.3.9。 -/
noncomputable def functorIsoOfSimplicialHomotopy {X Y : SSet.{u}} [KanComplex Y]
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) : FunctorIso f g := by
  let e := functorEdgeOfSimplicialHomotopy H
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom X).obj Y))
      (SSet.Truncated.HomotopyCategory.homMk e)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 概要：Kan 複体間の単体的ホモトピー同値は quasicategory の同値。
方針：二つの合成のホモトピーを可逆な関手の二胞体にする。
規約：両対象の Kan 性を仮定する。
使われ方：Kerodon Remark 4.8.3.9 の写像空間の同値。 -/
lemma IsSimplicialHomotopyEquivalence.isQCatEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {f : X ⟶ Y} (hf : IsSimplicialHomotopyEquivalence f) :
    IsQCatEquivalence f := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  exact ⟨g, ⟨functorIsoOfSimplicialHomotopy H⟩, ⟨functorIsoOfSimplicialHomotopy K⟩⟩

/-- 概要：Kan 複体間では実際のホモトピー逆の存在と quasicategory の同値性は同値。
方針：可逆二胞体と実際のホモトピーの二つの変換を使う。
規約：π₀ の全単射だけには置き換えない。
使われ方：Kerodon Remark 4.8.3.9。 -/
@[kerodon 03K1]
lemma isSimplicialHomotopyEquivalence_iff_isQCatEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence f ↔ IsQCatEquivalence f :=
  ⟨IsSimplicialHomotopyEquivalence.isQCatEquivalence,
    IsQCatEquivalence.isSimplicialHomotopyEquivalence⟩

end SerrePositivity.InfinityCategories
