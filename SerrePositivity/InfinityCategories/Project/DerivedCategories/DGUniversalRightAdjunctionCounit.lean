module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitMappingAdjunctionRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalRightAdjunction
/-!
概要：普遍余単位から作った随伴の余単位は、元の厳密切断の同じ実余単位である。
方針：全パラメータ Hom 対応の恒等射と、反対側の指定単位の回収を使う。
規約：元の h Fun の射を等式で保持する。使われ方：実 RHom 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed Bicategory SSet
open scoped _root_.Simplicial

/-- 構成した普遍随伴の余単位は、元の厳密切断の同じ実余単位。 -/
lemma dgUniversalRightAdjunction_counitHom
    (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
    [DifferentialGraded.DGCategory R C] [DifferentialGraded.DGCategory R E]
    (F : DifferentialGraded.DGFunctor R C E)
    (h : ∀ y : E, Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniversalCounit R C E F y)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjunction R C E F h).counitHom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniversalRightAdjointCounit R C E F h :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.qcatAdjunctionOfCounitIntervalCondition_counitHom _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
