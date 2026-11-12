module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonNative
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition

/-!
概要：D の固定 ε 商作用を、工程 1 が使用する native core 間の全単体射へ送る。
方針：既存 dg 関手の dg nerve を取り、native Kan core へ制限する。
規約：商 Hom 作用は D の正本をそのまま使用。工程 1 の射の存在は未主張。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (S : Set C) (T : Set D)

/-- D の同じ ε 整合関手圏の native core。 -/
def quotientEpsilonNativeCore : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeSpace R C D S T

instance quotientEpsilonNativeCore_kan :
    SSet.KanComplex (quotientEpsilonNativeCore R C D S T) := by
  change SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T)) : SSet)
  infer_instance

/-- ε 整合関手の同じ頂点。 -/
def quotientEpsilonNativeVertex (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    (quotientEpsilonNativeCore R C D S T).obj (Opposite.op ⦋0⦌) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex _⟩

/-- 工程 2 の dg 関手を native core 上で消費する全単体射。 -/
def quotientNativeInputMap :
    quotientEpsilonNativeCore R C D S T ⟶
      dgFunctorNativeMappingSpace R (DGQuotient.QuotientObject C S)
        (DGQuotient.QuotientObject D T) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap R C D S T

/-- 頂点作用は同じ正本 quotientDGFunctor と厳密に一致する。 -/
lemma quotientNativeInputMap_vertex (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    (quotientNativeInputMap R C D S T).app (Opposite.op ⦋0⦌)
        (quotientEpsilonNativeVertex R C D S T F) =
      dgFunctorNativeMappingVertex R _ _
        (DGQuotient.quotientDGFunctor R C D F.val S T F.property) := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- D-S の公開入口を固有名にし、D の同名の忘却公開と衝突させない。 -/
def quotientNativeInputForget :
    quotientEpsilonNativeCore R C D S T ⟶ dgFunctorNativeMappingSpace R C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C D S T))

lemma quotientNativeInputForget_vertex (F : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C D S T) :
    (quotientNativeInputForget R C D S T).app (Opposite.op ⦋0⦌)
        (quotientEpsilonNativeVertex R C D S T F) =
      dgFunctorNativeMappingVertex R C D F.val := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

omit [DGCategory R D] [Small.{u} D] in
/-- 工程 1 の単位保存に使う、D の正本 ε core の単位。 -/
def quotientNativeInputUnit :
    𝟙_ SSet.{max u v} ⟶ quotientEpsilonNativeCore R C C S S :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeUnit R C S

omit [DGCategory R D] [Small.{u} D] in
/-- native 消費射は同じ実商の単位を全単体で保つ。 -/
lemma quotientNativeInputMap_unit :
    quotientNativeInputUnit R C S ≫ quotientNativeInputMap R C C S S =
      dgFunctorNativeIdentity R (DGQuotient.QuotientObject C S) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonNativeMap_unit R C S

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
