module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import Mathlib.Logic.Small.Basic

/-!
概要：対象作用を固定した単体的な豊穣関手の小ささ。
方針：関手を固定した対象間の Hom の作用の族へ単射で符号化する。
規約：標的の対象全体は大きくてもよいが、豊穣 Hom の宇宙は u とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な unstraightening の小さい代表への宇宙調整。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：対象作用を固定した豊穣関手を、その Hom の作用の族で符号化する。
方針：対象作用の等式で Hom の終域を固定した対象の Hom に移す。
規約：単位則と合成則の証明は符号化の値に含めない。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な単体の対象を固定した小ささの証明。 -/
def enrichedFunctorFixedObjectCode {A : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D] (obj : A → D)
    (F : {F : EnrichedFunctor SSet.{u} A D // F.obj = obj}) :
    ∀ i j : A, (i ⟶[SSet.{u}] j) ⟶ (obj i ⟶[SSet.{u}] obj j) :=
  F.property ▸ F.val.map

/-- 概要：対象作用を固定した豊穣関手は Hom の作用の族で一意に決まる。
方針：二つの関手の構造を分解し、対象作用の等式を消去して写像部分を比較する。
規約：法則の証明の違いは証明無関係性で除かれる。
使われ方：Kerodon §2.4.3（Tag 00KM）、大きい豊穣関手の集合を小さい型へ埋め込む。 -/
lemma enrichedFunctorFixedObjectCode_injective {A : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D] (obj : A → D) :
    Function.Injective (enrichedFunctorFixedObjectCode obj) := by
  rintro ⟨⟨fo, fm, fi, fc⟩, hf⟩ ⟨⟨go, gm, gi, gc⟩, hg⟩ h
  change fo = obj at hf
  change go = obj at hg
  subst fo
  subst go
  change fm = gm at h
  subst gm
  rfl

/-- 概要：小さい対象型からの、対象作用を固定した豊穣関手の型は小さい。
方針：小さい Hom の作用の族への単射に小ささを引き戻す。
規約：標的 D の対象全体の小ささは要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent nerve の単体の対象を固定した宇宙縮小。 -/
instance enrichedFunctor_fixedObjects_small {A : Type v} {D : Type w}
    [Small.{u} A] [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} D]
    (obj : A → D) : Small.{u} {F : EnrichedFunctor SSet.{u} A D // F.obj = obj} :=
  small_of_injective (enrichedFunctorFixedObjectCode_injective obj)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
