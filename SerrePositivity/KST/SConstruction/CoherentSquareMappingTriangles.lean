module
public import SerrePositivity.KST.SConstruction.CoherentTriangleMappingEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.SquareComposition

/-! # 自然性 square の元の対角辺と二つの実三角形
概要：四辺を指定した square から共通の通常の対角射と二つの指定三角形を回収する。
方針：区間の積の二つの標準三角形を元の square で写し、同じ対角辺を復号する。
規約：値域の quasicategory 性も局所 Kan 性も仮定しない。
使われ方：二つの元の実三角形を写像空間の指定された二辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {X₀ X₁ Y₀ Y₁ : C}

/-- 元の四辺を保持する、共通の対角射と二つの実三角形。 -/
structure CoherentSquareMappingTriangles
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (l : X₀ ⟶ Y₀) (r : X₁ ⟶ Y₁) where
  /-- 元の square の対角辺から復号した通常の射。 -/
  diagonal : X₀ ⟶ Y₁
  /-- 下辺・右辺・元の対角辺の実三角形。 -/
  bottomRight : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge diagonal)
  /-- 左辺・上辺・同じ対角辺の実三角形。 -/
  leftTop : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge diagonal)

/-- 元の二つの三角形の第一のものから、対角射から下・右合成への写像空間の辺。 -/
def coherentSquareMappingBottomRight {f : X₀ ⟶ X₁} {g : Y₀ ⟶ Y₁}
    {l : X₀ ⟶ Y₀} {r : X₁ ⟶ Y₁} (T : CoherentSquareMappingTriangles f g l r) :
    (SimplicialCategory.sHom X₀ Y₁).Edge (SimplicialCategory.homEquiv' _ _ T.diagonal)
      (SimplicialCategory.homEquiv' _ _ (f ≫ r)) :=
  coherentTriangleMappingEdge f r T.diagonal T.bottomRight

/-- 元の二つの三角形の第二のものから、同じ対角射から左・上合成への写像空間の辺。 -/
def coherentSquareMappingLeftTop {f : X₀ ⟶ X₁} {g : Y₀ ⟶ Y₁}
    {l : X₀ ⟶ Y₀} {r : X₁ ⟶ Y₁} (T : CoherentSquareMappingTriangles f g l r) :
    (SimplicialCategory.sHom X₀ Y₁).Edge (SimplicialCategory.homEquiv' _ _ T.diagonal)
      (SimplicialCategory.homEquiv' _ _ (l ≫ g)) :=
  coherentTriangleMappingEdge l g T.diagonal T.leftTop

/-- 四辺の raw な一単体を保持し、元の square の二つの標準三角形を回収する。 -/
def coherentSquareMappingTrianglesOfEdges
    (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁) (l : X₀ ⟶ Y₀) (r : X₁ ⟶ Y₁)
    (Q : (Δ[1] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C)
    (hb : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
      (SSet.stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (ht : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
      (SSet.stdSimplex.obj₀Equiv.symm 1))).map ((truncation 2).map Q)).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge)
    (hl : (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
      (SSet.stdSimplex.obj₀Equiv.symm 0)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
        ((truncation 2).map Q)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge l).edge)
    (hr : (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
      (SSet.stdSimplex.obj₀Equiv.symm 1)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map
        ((truncation 2).map Q)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).edge) :
    CoherentSquareMappingTriangles f g l r := by
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
    (SSet.stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)
  let er := ((SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{max u v}))
    (SSet.stdSimplex.obj₀Equiv.symm 1)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  let ed := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map Q)
  have hx : Q.app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm 0, SSet.stdSimplex.obj₀Equiv.symm 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X₀ :=
    b.src_eq.symm.trans ((congrArg ((SimplicialNerve C).map
      (SimplexCategory.δ (1 : Fin 2)).op) hb).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).src_eq)
  have hy : Q.app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm 1, SSet.stdSimplex.obj₀Equiv.symm 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y₁ :=
    er.tgt_eq.symm.trans ((congrArg ((SimplicialNerve C).map
      (SimplexCategory.δ (0 : Fin 2)).op) hr).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge r).tgt_eq)
  let diag : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y₁) :=
    SSet.Edge.ofTruncated ⟨ed.edge, ed.src_eq.trans hx, ed.tgt_eq.trans hy⟩
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom diag
  have hd : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge = ed.edge :=
    congrArg SSet.Edge.edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom diag)
  let t₀ := ((SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  let t₁ := ((SSet.Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
    (SSet.Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map Q)
  refine ⟨d, ?_, ?_⟩
  · exact SSet.Edge.CompStruct.ofTruncated
      ⟨t₀.simplex, t₀.d₂.trans hb, t₀.d₀.trans hr, t₀.d₁.trans hd.symm⟩
  · exact SSet.Edge.CompStruct.ofTruncated
      ⟨t₁.simplex, t₁.d₂.trans hl, t₁.d₀.trans ht, t₁.d₁.trans hd.symm⟩

end SerrePositivity.KST.SConstruction
