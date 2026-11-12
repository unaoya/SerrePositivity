module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransWhisker

/-!
概要：元全厳密比較の合成等号を同じ dg 後合成で保持する。
方針：元 dg 関手の全斉次合成保存を閉零成分へ適用する。
規約：元全厳密自然変換の等号として保持する。
使われ方：元実 connecting の逆 shift 後の指定合成面。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

/-- 概要：元全厳密合成は同じ dg 後合成と交換する。
方針：元閉零成分の全斉次合成保存と外延性を使用する。
規約：元全比較を保持。使われ方：指定 connecting 合成の逆 shift。 -/
lemma dgStrictCompositionPostcomp {R : Type u} [CommRing R]
    {P D E : Type v} [DGCategory R P] [DGCategory R D] [DGCategory R E]
    {F G H : DGFunctor R P D} (α : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (β : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)
    (Q : DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp α Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp β Q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp α β) Q := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose Q (β.app x).val (α.app x).val (add_zero 0)).symm
end SerrePositivity.KST.SConstruction
