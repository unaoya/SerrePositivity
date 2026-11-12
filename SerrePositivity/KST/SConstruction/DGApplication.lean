module
public import SerrePositivity.KST.SConstruction.StableModels
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedFunctorExact

/-! # 厳密 dg 入力の S 構成への接続
概要：前三角 dg 圏と厳密 dg 関手を、安定な入力と完全な射へ送る。
方針：native dg nerve の安定性・完全性を既存の S 構成の保存条件に移す。
規約：一般 dg 圏への K は Perf 模型を経由する。豊穣 BF 関手の完成は別工程。
使われ方：K-4d の dg 関手性と Perf の Morita 比較への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded

/-- 完全な実単体的射は、S 構成の零対象・cofiber 保存条件を満たす。 -/
lemma preservesCofiberData_of_isExactFunctor {X Y : SSet.{u}} (f : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] : PreservesCofiberData f :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero, fun t ht => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber t ht⟩

variable (A : Type u) [CommRing A] (D E T : Type u)
  [DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
  [DGCategory A E] [Small.{u} E] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A E]
  [DGCategory A T] [Small.{u} T] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A T]

/-- 前三角 dg 圏の native nerve を、同じ宇宙の安定な入力へ束ねる。 -/
def dgStableModel : StableModel.{u} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D
  quasicategory := inferInstance
  stable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated A D

/-- 厳密 dg 関手が誘導する射は native nerve の射そのもの。 -/
def dgStableMap (F : DGFunctor A D E) : dgStableModel A D ⟶ dgStableModel A E := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedFunctor_isExactFunctor A D E F
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F, preservesCofiberData_of_isExactFunctor _⟩

/-- dg 関手の恒等射は、安定な入力の恒等射に厳密に一致する。 -/
lemma dgStableMap_id : dgStableMap A D D (DGFunctor.id D) = 𝟙 (dgStableModel A D) :=
  Subtype.ext _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id

/-- dg 関手の合成は、安定な入力の合成に厳密に一致する。 -/
lemma dgStableMap_comp (F : DGFunctor A D E) (G : DGFunctor A E T) :
    dgStableMap A D T (F.comp G) = dgStableMap A D E F ≫ dgStableMap A E T G :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp F G)

end SerrePositivity.KST.SConstruction
