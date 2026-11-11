module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleIdentity

/-!
概要：元の補正成分と大域自然性の指定合成は、共有頂点で直接自然性を回収する。
方針：前合成した補正 path の指定像を、元の自然性の三角等式へ貼り合わせる。
規約：補正 path と元の三辺を選び直さない。
使われ方：元の分類 Hom 作用と補正 pullback 比較の同定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 補正成分と元の大域自然性の合成は、共有頂点で同じ直接自然性を回収する。 -/
lemma PathCorrectedFunctorSquare.globalComposite_postcomp_heq
    {H A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {q : X ⟶ Y} {f : A ⟶ X} {g : A ⟶ Y} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
    (s : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedFunctorSquare q f g e) (r : H ⟶ A)
    {t : H ⟶ X} (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (r ≫ f) t)
    {a' b' t' : H ⟶ Y} (E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' b') (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso b' t')
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a' t') (ha : (r ≫ s.map) ≫ q = a')
    (hb : (r ≫ f) ≫ q = b') (ht : t ≫ q = t')
    (he : HEq (e.precomp r) E) (hk : HEq (n.postcomp q) K)
    (h : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.IsoTriangleCommutes E K D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (s.exactComponentIso.precomp r ≪≫ n) q) D := by
  have hc := (s.exactComponentIso_precomp_postcomp_heq r).trans he
  have hp := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.iso_pasting_heq_of_endpoint_eq
    ((s.exactComponentIso.precomp r).postcomp q) (n.postcomp q) E K
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) ha)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) hb)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) ht) hc.symm hk.symm
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans (s.exactComponentIso.precomp r) n q)).trans
    (hp.trans (heq_of_eq h))

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
