module
public import SerrePositivity.KST.Fibration.ZeroEndPostcompFamily
public import SerrePositivity.KST.Fibration.VerdierNullCompositeVertices
public import SerrePositivity.KST.Fibration.VerdierNullHomRelativeComparison
public import SerrePositivity.KST.Fibration.FixedRestrictionFunctorPrism

/-! # 元の零自己関手円柱と指定 Verdier 二胞体の、実合成頂点を固定した比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定 Verdier 二胞体の、元の共有対角から同じ二短辺合成への実 path 族。 -/
def verdierNullPathFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (Δ[1] : SSet.{u}) ⟶
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
        (verdierNullDiagonal d).obj ⟨ULift.up 1⟩) :=
  SSet.yonedaEquiv.symm (nerve.edgeMk
    (coherentTriangleDirectToPath coherentTriangleFullPath)).edge ≫ verdierNullHomFamily d j

/-- 同じ指定 path 族の終端は、元の二短辺の合成 path の同じ実頂点。 -/
theorem verdierNullPathFamily_one (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    stdSimplex.δ (0 : Fin 2) ≫ verdierNullPathFamily d j =
      SSet.yonedaEquiv.symm (verdierNullCompositeVertex d j) := by
  unfold verdierNullPathFamily
  rw [SSet.yonedaEquiv_symm_comp]
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ((nerve.edgeMk (coherentTriangleDirectToPath coherentTriangleFullPath)).map
    (verdierNullHomFamily d j)).toTruncated.tgt_eq

/-- 元の指定 path 族の全頂点は、同じ実零値関手条件を保つ。 -/
theorem verdierNullPathFamily_zero (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2)
    (v : (Δ[1] : SSet.{u}) _⦋0⦌) :
    StableHomZeroVertex _ _ ((verdierNullPathFamily d j).app (Opposite.op ⦋0⦌) v) :=
  verdierNullHomFamily_zero d j _

/-- 元の下側二胞体の実合成を指定した、同じ零自己関手円柱の元の Kan Hom 像。 -/
def verdierNullContractionFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (Δ[1] : SSet.{u}) ⟶
      ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩ ⟶[SSet.{u}]
        (verdierNullDiagonal d).obj ⟨ULift.up 1⟩) :=
  zeroEndPostcompFamily (verdierNullCompositeMap d 1)
    (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeMap_zero d 1))

/-- 元の円柱像と指定下側二胞体族は、元の実合成頂点を全比較時刻で固定して結ぶ。 -/
def verdierNullContractionComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (verdierNullContractionFamily d) (verdierNullPathFamily d 1) := by
  apply zeroStableHomFamilyRelativeComparison
  · exact zeroEndPostcompFamily_zero_vertices _ _
  · exact verdierNullPathFamily_zero d 1
  · exact (zeroEndPostcompFamily_one _ _).trans
      ((congrArg SSet.yonedaEquiv.symm
        (stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d 1))).trans
          (verdierNullPathFamily_one d 1).symm)

/-- 同じ比較は、元の全正反復 S• の全 Hom 作用後にも実合成頂点を固定する。 -/
def verdierNullContractionMultiComparison (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (verdierNullContractionFamily d ≫ (stableMultiKanEnrichedFunctor r).map _ _)
      (verdierNullPathFamily d 1 ≫ (stableMultiKanEnrichedFunctor r).map _ _) :=
  (verdierNullContractionComparison d).postcomp _

/-- 元の比較円柱は、指定した実合成端上で同じ恒等族へ厳密に制限する。 -/
theorem verdierNullContractionComparison_fixed (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2)) ≫
        (verdierNullContractionComparison d).prism =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        stdSimplex.δ (0 : Fin 2) ≫ verdierNullContractionFamily d :=
  (verdierNullContractionComparison d).prism_restriction

end SerrePositivity.KST.Fibration
