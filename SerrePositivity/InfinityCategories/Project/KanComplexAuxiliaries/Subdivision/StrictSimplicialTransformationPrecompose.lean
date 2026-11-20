module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformation

/-! # 厳密単体的自然変換の全入力上の前合成
概要：元の全 Hom の高次作用を保って、厳密自然変換を任意の豊穣入力関手へ制限する。
方針：元の自然性を、入力関手の全単体の像で評価する。
規約：入力 Hom を離散化しない。使われ方：厳密 dg 入力上の suspension 比較。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 全 Hom に自然な厳密単体的自然変換は、元の豊穣入力関手で前合成できる。 -/
def strictSimplicialTransformationPrecompose
    {C : Type v} {D : Type w} {E : Type z}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    [EnrichedCategory SSet.{u} E]
    (H : EnrichedFunctor SSet.{u} C D) (F G : EnrichedFunctor SSet.{u} D E)
    (τ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (H.comp SSet F) (H.comp SSet G) where
  app X := τ.app (H.obj X)
  naturality X Y := by
    ext n t
    exact types_congr_hom (NatTrans.congr_app (τ.naturality (H.obj X) (H.obj Y)) n)
      (t.1, (H.map X Y).app n t.2)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
