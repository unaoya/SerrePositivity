module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation

/-! # 全成分を保つ厳密豊穣自然変換の始域の括弧付け
概要：三つの豊穣関手の合成の括弧だけを変更し、元の厳密自然変換の全成分を保持する。
方針：同じ全単体の写像作用で元の自然性を評価する。
規約：同型成分の選択や持ち上げは行わない。使われ方：Ex∞ 組み立ての右脚の合成。
-/
@[expose] public section
noncomputable section
universe u v w x y
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 三重合成の始域の括弧を変えても、同じ全成分の厳密自然変換を保つ。 -/
def strictSimplicialTransformationReassociateSource
    {C : Type v} {D : Type w} {E : Type x} {T : Type y}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    [EnrichedCategory SSet.{u} E] [EnrichedCategory SSet.{u} T]
    (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E)
    (H : EnrichedFunctor SSet.{u} E T) (K : EnrichedFunctor SSet.{u} C T)
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      ((F.comp SSet G).comp SSet H) K) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) (F.comp SSet (G.comp SSet H)) K where
  app X := η.app X
  naturality X Y := by
    ext n t
    exact types_congr_hom (NatTrans.congr_app (η.naturality X Y) n) t

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
