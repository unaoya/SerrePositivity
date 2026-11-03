module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutCosliceRestriction
public import SerrePositivity.InfinityCategories.F1.CoconeMappingRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedCosliceRestrictionComposition
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.KanSquareFiberEquivalence

/-!
概要：pushout 四角形の指定左辺上の fiber と、入力 span の指定右枝上の fiber を比較する。
方針：元の span への自明 Kan 制限を、同じ指定余錐の fiber に制限する。
規約：指定した基点と固定終点を保持する。高次の比較を零次元の全射に弱めない。
使われ方：HTT 5.5.5.13 の pushout による写像空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
attribute [local instance] coconeMappingSpace_kanComplex
  vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C] (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)

/-- 入力 span の右枝を、元の四角形の左辺の表示に揃えて制限する。 -/
def pushoutSpanRightMappingRestriction (y : C _⦋0⦌) :
    coconeMappingSpace (pushoutSpan R) y ⟶ coconeMappingSpace (squareLeftEdge ≫ R) y :=
  normalizedCoconeRestrictionFiber (pushoutSpan R) horn₂₀.ι₀₂
    (by rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]) y

/-- 四角形から span を経る元の左辺への制限は、直接の制限と厳密に一致する。 -/
lemma pushoutSpanRightMappingRestriction_comp (y : C _⦋0⦌) :
    cosliceRestrictionFiberMap R spanSquareBoundary y ≫
        pushoutSpanRightMappingRestriction R y =
      cosliceRestrictionFiberMap R squareLeftEdge y := by
  have h := normalizedCoconeRestrictionFiber_twoStep R spanSquareBoundary (pushoutSpan R) rfl
    horn₂₀.ι₀₂ (squareLeftEdge ≫ R)
    (by rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge])
    squareLeftEdge spanSquareBoundary_leftEdge rfl y
  simpa only [pushoutSpanRightMappingRestriction, normalizedCoconeRestrictionFiber_eq,
    eqToHom_refl, Category.comp_id, Category.assoc]
    using h

/-- 正規化した元の右枝の制限も、全ホーンに関する fibration。 -/
lemma pushoutSpanRightMappingRestriction_fibration (y : C _⦋0⦌) :
    Fibration (pushoutSpanRightMappingRestriction R y) := by
  have : Mono (horn₂₀.ι₀₂ : (Δ[1] : SSet.{u}) ⟶ horn 2 0) :=
    mono_of_mono_fac (horn.ι_ι (0 : Fin 3) 1 (by decide))
  have := coconeMappingSpace_restrict_fibration (pushoutSpan R) horn₂₀.ι₀₂ y
  rw [pushoutSpanRightMappingRestriction, normalizedCoconeRestrictionFiber_eq]
  infer_instance

/-- 元の左辺上の任意の基点で、四角形と span の実際の fiber の比較を取る。 -/
def pushoutSpanMappingFiberComparison (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    vertexFiber (cosliceRestrictionFiberMap R squareLeftEdge y) d ⟶
      vertexFiber (pushoutSpanRightMappingRestriction R y) d :=
  vertexFiberMap _ _ (cosliceRestrictionFiberMap R spanSquareBoundary y)
    (pushoutSpanRightMappingRestriction_comp R y) d

/-- pushout の同じ指定基点の fiber 比較は、全写像空間で同値となる。 -/
lemma pushoutSpanMappingFiberComparison_homotopyEquivalence
    (hR : IsPushoutSquare R) (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pushoutSpanMappingFiberComparison R y d) := by
  have : Mono (squareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b h
    exact congrArg Prod.snd h
  have := coconeMappingSpace_restrict_fibration R squareLeftEdge y
  have := pushoutSpanRightMappingRestriction_fibration R y
  have := pushoutCoconeMappingRestriction_trivialKanFibration R hR y
  have : KanComplex (coconeMappingSpace R y) := coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace (pushoutSpan R) y) := coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace (squareLeftEdge ≫ R) y) :=
    coconeMappingSpace_kanComplex _ _
  have h := kanSquareFiberMap_isQCatEquivalence
    (cosliceRestrictionFiberMap R squareLeftEdge y) (pushoutSpanRightMappingRestriction R y)
    (cosliceRestrictionFiberMap R spanSquareBoundary y) (𝟙 _)
    ((pushoutSpanRightMappingRestriction_comp R y).trans (Category.comp_id _).symm) d
    (isQCatEquivalence_of_trivialKanFibration _)
    (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
