module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentPathDual

/-!
概要：単体的豊穣関手の反対と simplicial thickening の順序双対への自然性。
方針：Hom を逆順の二端点で評価し、合成の対称性と path の像の可換性を使う。
規約：SSet 自体は反転せず、豊穣圏の反対だけを取る。
使われ方：Kerodon §4.6.7（Tag 01LA） の左右の比較と、HTT 4.2.4.1 の係数の向きの検証。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z t
open CategoryTheory MonoidalCategory BraidedCategory CartesianMonoidalCategory SSet
open SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体的豊穣関手は反対の豊穣圏の間の関手を誘導する。
方針：対象を反対へ移し、Hom の二端点を逆順にする。
規約：反対の合成の対称性は元の豊穣関手の合成則と整合する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の構成。 -/
def coherentEnrichedFunctorOp {C : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet C D) : EnrichedFunctor SSet Cᵒᵖ Dᵒᵖ where
  obj x := Opposite.op (F.obj x.unop)
  map x y := F.map y.unop x.unop
  map_id x := F.map_id x.unop
  map_comp x y z := by
    rw [eComp_op_eq, Category.assoc, F.map_comp, ← braiding_naturality_assoc, eComp_op_eq]

/-- 概要：豊穣関手の反対は豊穣関手の合成を保つ。
方針：対象と Hom の射を定義から比較する。
規約：合成の順序は変えず、各関手の始域と終域を反対へ移す。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の自然性。 -/
lemma coherentEnrichedFunctorOp_comp {C : Type v} {D : Type w} {E : Type z}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    [EnrichedCategory SSet.{u} E] (F : EnrichedFunctor SSet C D)
    (G : EnrichedFunctor SSet D E) :
    coherentEnrichedFunctorOp (F.comp SSet G) =
      (coherentEnrichedFunctorOp F).comp SSet (coherentEnrichedFunctorOp G) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) (fun _ _ => ?_)
  exact Category.comp_id _

/-- 概要：単体的豊穣関手の合成は結合的である。
方針：対象は定義から一致し、Hom の射には圏の合成の結合則を使う。
規約：豊穣先は SSet に固定する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の添字変換の整理。 -/
lemma coherentEnrichedFunctor_comp_assoc {B : Type v} {C : Type w} {D : Type z}
    {E : Type t} [EnrichedCategory SSet.{u} B] [EnrichedCategory SSet.{u} C]
    [EnrichedCategory SSet.{u} D] [EnrichedCategory SSet.{u} E]
    (F : EnrichedFunctor SSet B C) (G : EnrichedFunctor SSet C D)
    (H : EnrichedFunctor SSet D E) :
    (F.comp SSet G).comp SSet H = F.comp SSet (G.comp SSet H) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) (fun _ _ => ?_)
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id, Category.assoc]
  rfl

/-- 概要：thickening の順序双対への反転は単調写像による豊穣関手に自然。
方針：同じ集合の像を先に取るか、順序双対へ移してから取るかを比較する。
規約：包含順序と単調写像の像は元の向きで保持する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent simplex の添字変換。 -/
lemma coherentThickeningDual_naturality {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) :
    (SimplicialThickening.functor f).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentThickeningDual K) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentThickeningDual J).comp SSet
        (coherentEnrichedFunctorOp (SimplicialThickening.functor f.dual)) := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) (fun i j => ?_)
  change nerveMap (SimplicialThickening.functorMap f i j) ≫
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPathDualFunctor (f i.as) (f j.as)) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPathDualFunctor i.as j.as) ≫
      nerveMap (SimplicialThickening.functorMap f.dual
        ⟨OrderDual.toDual j.as⟩ ⟨OrderDual.toDual i.as⟩)
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun _ => ?_)
  apply SimplicialThickening.Path.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
