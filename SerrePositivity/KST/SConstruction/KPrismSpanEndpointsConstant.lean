module
public import SerrePositivity.KST.SConstruction.KPrismCompositionFaceValues
public import SerrePositivity.KST.SConstruction.KPrismNativeSpanTargets
public import SerrePositivity.KST.SConstruction.CoherentRefinementPathVertices

/-! # 元の上下の K 円柱の終点族は二辺の元の値の定数族
概要：全精密化をパラメータとする上下の native 終点族を、元の二辺の因子分解の値へ厳密に戻す。
方針：同じ最終列内の合成面の定数性と、元の二辺の列からの精密化を使う。
規約：元の円柱と native Hom を保持し、新たなホモトピーや代表辺を選ばない。
使われ方：元の構造射と段の写像の二合成を全パラメータで照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismSpanEndpointsConstant_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下側の元の全終点族は、元の二辺の因子分解列の値の定数族そのもの。 -/
lemma kKanOriginalPrismLowerNativeFamily_eq_const {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismLowerNativeFamily r F f =
      SSet.const ((kKanOriginalPrismLowerNativeFamily r F f).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro S
  let t := S.obj (Fin.last d)
  let a := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringMap (coherentArrowStringDirectTo t)
  let m := coherentStringNativeMap (kKanOriginalPrismStringDiagram r F) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString t)
  let E := SimplicialCategory.sHom
    (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (x, ULift.up 0))
    (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (y, ULift.up 1))
  let v : E _⦋0⦌ := (kKanOriginalPrismLowerNativeFamily r F f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
  let p := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a
  let q := (nerve (SimplicialThickening.Path
    (ULift.up 0 : ULift.{u} (Fin (t.length + 2)))
    (ULift.up (Fin.last (t.length + 1))))).map
      (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)
  have hq : q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last t.length).castSucc)).obj (Opposite.op ⦋d⦌) := by
    intro k
    exact coherentLowerPrismRefinementPath_cut (coherentArrowStringDirectTo t)
  have h₀ := kKanOriginalPrismLowerNativeValues_eq r F t d
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (S ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)) q
      (coherentLowerPrismPathFlag_through S) hq
  have h₁ := coherentStringNativeMap_refinementVertex (kKanOriginalPrismStringDiagram r F) a
  have h₂ := coherentPrismLowerNativeFamily_vertex (kKanOriginalPrismStringDiagram r F) f
    (coherentArrowStringDirect f)
  have hv : m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p) = v := h₁.trans h₂.symm
  have hn := NatTrans.naturality_apply m (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)
  change m.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (S ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)) = _
  exact h₀.trans (hn.trans (congrArg (E.map (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op) hv))

/-- 上側の元の全終点族は、元の二辺の因子分解列の値の定数族そのもの。 -/
lemma kKanOriginalPrismUpperNativeFamily_eq_const {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismUpperNativeFamily r F f =
      SSet.const ((kKanOriginalPrismUpperNativeFamily r F f).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro S
  let t := S.obj (Fin.last d)
  let a := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringMap (coherentArrowStringDirectTo t)
  let m := coherentStringNativeMap (kKanOriginalPrismStringDiagram r F) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString t)
  let E := SimplicialCategory.sHom
    (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (x, ULift.up 0))
    (coherentStringVertexObject (kKanOriginalPrismStringDiagram r F) (y, ULift.up 1))
  let v : E _⦋0⦌ := (kKanOriginalPrismUpperNativeFamily r F f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))
  let p := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath a
  let q := (nerve (SimplicialThickening.Path
    (ULift.up 0 : ULift.{u} (Fin (t.length + 2)))
    (ULift.up (Fin.last (t.length + 1))))).map
      (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)
  have hq : q ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up ((0 : Fin (t.length + 1)).succ))).obj (Opposite.op ⦋d⦌) := by
    intro k
    exact coherentUpperPrismRefinementPath_cut (coherentArrowStringDirectTo t)
  have h₀ := kKanOriginalPrismUpperNativeValues_eq r F t d
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (S ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)) q
      (coherentUpperPrismPathFlag_through S) hq
  have h₁ := coherentStringNativeMap_refinementVertex (kKanOriginalPrismStringDiagram r F) a
  have h₂ := coherentPrismUpperNativeFamily_vertex (kKanOriginalPrismStringDiagram r F) f
    (coherentArrowStringDirect f)
  have hv : m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p) = v := h₁.trans h₂.symm
  have hn := NatTrans.naturality_apply m (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex p)
  change m.app (Opposite.op ⦋d⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (S ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)) = _
  exact h₀.trans (hn.trans (congrArg (E.map (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op) hv))

/-- 元の suspension 写像空間の下側の終点族も、元の二辺の値の定数族そのもの。 -/
lemma kKanOriginalPrismLowerSuspensionFamily_eq_const {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismLowerSuspensionFamily r F f =
      SSet.const ((kKanOriginalPrismLowerSuspensionFamily r F f).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) := by
  have h := congrArg (fun m => m ≫ (kKanOriginalPrismNativeHomIso r F x y).hom)
    (kKanOriginalPrismLowerNativeFamily_eq_const r F f)
  exact h.trans (SSet.const_comp _ _)

/-- 元の二辺の因子分解による下側の終点を、元の suspension 写像空間の頂点として表示する。 -/
def kKanOriginalPrismLowerEndpointVertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalSuspensionMappingTarget r F x y) _⦋0⦌ :=
  (kKanOriginalPrismLowerSuspensionFamily r F f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))

/-- 元の長辺から元の二辺の下側の値への、両端が定数の同じ実円柱。 -/
def kKanOriginalPrismLowerEndpointContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))
      (kKanOriginalPrismSpanInitialVertex r F f))
      (SSet.const (kKanOriginalPrismLowerEndpointVertex r F f)) := by
  let H := kKanOriginalPrismLowerSuspensionContraction r F f
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁.trans (kKanOriginalPrismLowerSuspensionFamily_eq_const r F f)
      rel := H.rel }

/-- 両端を定数として表示しても、元の全パラメータの下側の実円柱は変わらない。 -/
lemma kKanOriginalPrismLowerEndpointContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismLowerEndpointContraction r F f).h =
      (kKanOriginalPrismLowerSuspensionContraction r F f).h := rfl

/-- 元の suspension 写像空間の上側の終点族も、元の二辺の値の定数族そのもの。 -/
lemma kKanOriginalPrismUpperSuspensionFamily_eq_const {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    kKanOriginalPrismUpperSuspensionFamily r F f =
      SSet.const ((kKanOriginalPrismUpperSuspensionFamily r F f).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))) := by
  have h := congrArg (fun m => m ≫ (kKanOriginalPrismNativeHomIso r F x y).hom)
    (kKanOriginalPrismUpperNativeFamily_eq_const r F f)
  exact h.trans (SSet.const_comp _ _)

/-- 元の二辺の因子分解による上側の終点を、元の suspension 写像空間の頂点として表示する。 -/
def kKanOriginalPrismUpperEndpointVertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalSuspensionMappingTarget r F x y) _⦋0⦌ :=
  (kKanOriginalPrismUpperSuspensionFamily r F f).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentArrowStringDirect f))

/-- 元の長辺から元の二辺の上側の値への、両端が定数の同じ実円柱。 -/
def kKanOriginalPrismUpperEndpointContraction {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    SSet.Homotopy (SSet.const (X := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f))
      (kKanOriginalPrismSpanInitialVertex r F f))
      (SSet.const (kKanOriginalPrismUpperEndpointVertex r F f)) := by
  let H := kKanOriginalPrismUpperSuspensionContraction r F f
  exact
    { h := H.h
      h₀ := H.h₀
      h₁ := H.h₁.trans (kKanOriginalPrismUpperSuspensionFamily_eq_const r F f)
      rel := H.rel }

/-- 両端を定数として表示しても、元の全パラメータの上側の実円柱は変わらない。 -/
lemma kKanOriginalPrismUpperEndpointContraction_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismUpperEndpointContraction r F f).h =
      (kKanOriginalPrismUpperSuspensionContraction r F f).h := rfl

end SerrePositivity.KST.SConstruction
