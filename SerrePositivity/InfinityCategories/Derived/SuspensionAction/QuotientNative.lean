module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonCategory
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  (S : Set C) (T : Set D)

/-- D の同じ ε 整合関手圏の native core。 -/
def quotientEpsilonNativeCore : SSet.{max u v} :=
  (quasicategoryCore (dgNerve R (NullPreservingFunctorsε R C D S T)) : SSet)

instance quotientEpsilonNativeCore_kan :
    SSet.KanComplex (quotientEpsilonNativeCore R C D S T) := by
  change SSet.KanComplex (quasicategoryCore
    (dgNerve R (NullPreservingFunctorsε R C D S T)) : SSet)
  infer_instance

/-- ε 整合関手の同じ頂点。 -/
def quotientEpsilonNativeVertex (F : NullPreservingFunctorsε R C D S T) :
    (quotientEpsilonNativeCore R C D S T).obj (Opposite.op ⦋0⦌) :=
  ⟨DGNerve.Simplex.vertex F, quasicategoryCore_vertex _⟩

/-- 工程 2 の dg 関手を native core 上で消費する全単体射。 -/
def quotientNativeInputMap :
    quotientEpsilonNativeCore R C D S T ⟶
      dgFunctorNativeMappingSpace R (DGQuotient.QuotientObject C S)
        (DGQuotient.QuotientObject D T) :=
  quasicategoryCoreMap (dgNerve.map (quotientInputFunctor R C D S T))

/-- 頂点作用は同じ正本 quotientDGFunctor と厳密に一致する。 -/
lemma quotientNativeInputMap_vertex (F : NullPreservingFunctorsε R C D S T) :
    (quotientNativeInputMap R C D S T).app (Opposite.op ⦋0⦌)
        (quotientEpsilonNativeVertex R C D S T F) =
      dgFunctorNativeMappingVertex R _ _
        (DGQuotient.quotientDGFunctor R C D F.val S T F.property) := by
  apply Subtype.ext
  apply DGNerve.Simplex.vertexEquiv.injective
  rfl

/-- 同じ ε core から、元の全次数関手圏の native core への忘却。 -/
def quotientEpsilonNativeForget :
    quotientEpsilonNativeCore R C D S T ⟶ dgFunctorNativeMappingSpace R C D :=
  quasicategoryCoreMap (dgNerve.map (nullPreservingFunctorsεForget R C D S T))

lemma quotientEpsilonNativeForget_vertex (F : NullPreservingFunctorsε R C D S T) :
    (quotientEpsilonNativeForget R C D S T).app (Opposite.op ⦋0⦌)
        (quotientEpsilonNativeVertex R C D S T F) =
      dgFunctorNativeMappingVertex R C D F.val := by
  apply Subtype.ext
  apply DGNerve.Simplex.vertexEquiv.injective
  rfl

end SerrePositivity.InfinityCategories
