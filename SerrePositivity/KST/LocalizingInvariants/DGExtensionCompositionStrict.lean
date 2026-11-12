module

public import SerrePositivity.KST.LocalizingInvariants.DGStrictCompositeCounit
public import SerrePositivity.KST.LocalizingInvariants.DGRestrictionCompositionStrict
public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCounitHomNaturality

/-!
概要：D の元の graph 延長の二重合成から合成 dg 関手の延長への厳密 dg 比較を作る。
方針：元の単位を制限合成の逆同型で輸送し、二つの元の余単位と組み合わせる。
規約：元の延長と全 Hom を保持。使われ方：Perf の実合成同型の nerve 移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T] (F : DGFunctor R D E) (G : DGFunctor R E T)

/-- 元の合成延長の単位を、二つの制限の合成へ輸送した厳密変換。 -/
def dgExtensionCompositionUnit : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id (RightModule R D))
    ((dgModuleExtension R D T (F.comp G)).comp
      ((dgModuleRestriction R E T G.op).comp (dgModuleRestriction R D E F.op))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgExtensionUnitStrict R D T (F.comp G))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp (dgModuleExtension R D T (F.comp G))
      (dgRestrictionCompositionInvStrict R D E T F G))

/-- 二つの元の余単位から得る、二重延長・二重制限の余単位。 -/
def dgExtensionCompositionCounit : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    (((dgModuleRestriction R E T G.op).comp (dgModuleRestriction R D E F.op)).comp
      ((dgModuleExtension R D E F).comp (dgModuleExtension R E T G)))
    (DGFunctor.id (RightModule R T)) :=
  dgStrictCompositeCounit (dgModuleExtension R D E F) (dgModuleExtension R E T G)
    (dgModuleRestriction R D E F.op) (dgModuleRestriction R E T G.op)
    (dgExtensionCounitStrict R D E F) (dgExtensionCounitStrict R E T G)

/-- 二重 graph 延長から、元の合成 dg 関手に沿う延長への全斉次自然な比較。 -/
def dgExtensionCompositionStrict : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans
    ((dgModuleExtension R D E F).comp (dgModuleExtension R E T G))
    (dgModuleExtension R D T (F.comp G)) :=
  dgStrictAdjointComparison _ _ _ (dgExtensionCompositionUnit R D E T F G)
    (dgExtensionCompositionCounit R D E T F G)

/-- 通常の随伴一意性による比較自然同型。厳密比較との成分照合は別工程。 -/
def dgExtensionCompositionIso :
    (dgModuleExtension R D E F).onClosed ⋙ (dgModuleExtension R E T G).onClosed ≅
      (dgModuleExtension R D T (F.comp G)).onClosed :=
  Adjunction.leftAdjointUniq
    ((dgModuleExtensionRestrictionAdjunction R D E F).comp
      (dgModuleExtensionRestrictionAdjunction R E T G))
    ((dgModuleExtensionRestrictionAdjunction R D T (F.comp G)).ofNatIsoRight
      (graphRestrictionCompositionIso R D E T F G).symm)

end SerrePositivity.KST.LocalizingInvariants
