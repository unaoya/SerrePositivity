module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutSpanMappingFiber

/-!
概要：四角形の指定左辺上の fiber を、上辺の始点制限の同じ fiber へ移す。
方針：上辺への制限と左辺の終点制限が共に自明 Kan となる正方形を使う。
規約：四角形自体には pushout 性を課さず、元の基点の像を保持する。
使われ方：HTT 5.5.5.13 の pushout 比較の第二段階。
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

/-- 元の正方形の左上頂点への二通りの点包含は一致する。 -/
lemma squareTopLeft_corner :
    stdSimplex.δ (1 : Fin 2) ≫ (squareTopEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) =
      stdSimplex.δ (0 : Fin 2) ≫ squareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 元の上辺の始点図式は、同じ左辺の終点図式である。 -/
lemma squareTopSource_eq_leftTarget :
    stdSimplex.δ (1 : Fin 2) ≫ (squareTopEdge ≫ R) =
      stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R) := by
  rw [← Category.assoc, squareTopLeft_corner, Category.assoc]

/-- 上辺の始点を元の左辺の終点の図式に揃えた、固定終点の制限。 -/
def squareTopSourceMappingRestriction (y : C _⦋0⦌) :
    coconeMappingSpace (squareTopEdge ≫ R) y ⟶
      coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) y :=
  normalizedCoconeRestrictionFiber (squareTopEdge ≫ R) (stdSimplex.δ (1 : Fin 2))
    (squareTopSource_eq_leftTarget R) y

/-- 上辺経由と左辺経由の、同じ頂点への元の制限は厳密に可換する。 -/
lemma squareTopSourceMappingRestriction_comp (y : C _⦋0⦌) :
    cosliceRestrictionFiberMap R squareTopEdge y ≫ squareTopSourceMappingRestriction R y =
      cosliceRestrictionFiberMap R squareLeftEdge y ≫
        cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y := by
  let w := stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1])
  have hw : stdSimplex.δ (1 : Fin 2) ≫ squareTopEdge = w := squareTopLeft_corner
  have ht : w ≫ R = stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R) := Category.assoc _ _ _
  have h₁ := normalizedCoconeRestrictionFiber_twoStep R squareTopEdge (squareTopEdge ≫ R) rfl
    (stdSimplex.δ (1 : Fin 2)) _ (squareTopSource_eq_leftTarget R) w hw ht y
  have h₂ := normalizedCoconeRestrictionFiber_twoStep R squareLeftEdge (squareLeftEdge ≫ R) rfl
    (stdSimplex.δ (0 : Fin 2)) _ rfl w rfl ht y
  simpa only [squareTopSourceMappingRestriction, normalizedCoconeRestrictionFiber_eq,
    eqToHom_refl, Category.comp_id, Category.assoc]
    using h₁.trans h₂.symm

/-- 正規化した同じ上辺の始点制限は全ホーンを持ち上げる。 -/
lemma squareTopSourceMappingRestriction_fibration (y : C _⦋0⦌) :
    Fibration (squareTopSourceMappingRestriction R y) := by
  have := coconeMappingSpace_restrict_fibration (squareTopEdge ≫ R)
    (stdSimplex.δ (1 : Fin 2)) y
  rw [squareTopSourceMappingRestriction, normalizedCoconeRestrictionFiber_eq]
  infer_instance

/-- 元の左辺上の指定基点を、その同じ終点制限の像へ送る fiber 比較。 -/
def pushoutTopMappingFiberComparison (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    vertexFiber (cosliceRestrictionFiberMap R squareLeftEdge y) d ⟶
      vertexFiber (squareTopSourceMappingRestriction R y)
        ((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y).app _ d) :=
  kanSquareFiberMap (cosliceRestrictionFiberMap R squareLeftEdge y)
    (squareTopSourceMappingRestriction R y) (cosliceRestrictionFiberMap R squareTopEdge y)
    (cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y)
    (squareTopSourceMappingRestriction_comp R y) d

/-- 同じ基点の上辺への比較は、全高次を含めて同値である。 -/
lemma pushoutTopMappingFiberComparison_homotopyEquivalence (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pushoutTopMappingFiberComparison R y d) := by
  have : Mono (squareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b h
    exact congrArg Prod.snd h
  have := coconeMappingSpace_restrict_fibration R squareLeftEdge y
  have := squareTopSourceMappingRestriction_fibration R y
  have := squareTopCoconeMappingRestriction_trivialKanFibration R y
  have := cosliceTriangleTarget_trivialKanFibration (squareLeftEdge ≫ R) y
  have : KanComplex (coconeMappingSpace R y) := coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace (squareTopEdge ≫ R) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace (squareLeftEdge ≫ R) y) :=
    coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace
      (stdSimplex.δ (0 : Fin 2) ≫ (squareLeftEdge ≫ R)) y) := coconeMappingSpace_kanComplex _ _
  exact (kanSquareFiberMap_isQCatEquivalence _ _ _ _ _ d
    (isQCatEquivalence_of_trivialKanFibration _)
    (isQCatEquivalence_of_trivialKanFibration _)).isSimplicialHomotopyEquivalence

/-- pushout の入力 span と上辺の同じ基点の fiber は、同じ可縮性を持つ。 -/
lemma pushoutMappingFiber_contractible_iff (hR : IsPushoutSquare R) (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    IsContractibleKan (vertexFiber (pushoutSpanRightMappingRestriction R y) d) ↔
      IsContractibleKan (vertexFiber (squareTopSourceMappingRestriction R y)
        ((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y).app _ d)) := by
  have : Mono (squareLeftEdge : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro a b h
    exact congrArg Prod.snd h
  have := coconeMappingSpace_restrict_fibration R squareLeftEdge y
  have := pushoutSpanRightMappingRestriction_fibration R y
  have := squareTopSourceMappingRestriction_fibration R y
  exact (pushoutSpanMappingFiberComparison_homotopyEquivalence R hR y d).isContractibleKan_iff.symm.trans
    (pushoutTopMappingFiberComparison_homotopyEquivalence R y d).isContractibleKan_iff

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
