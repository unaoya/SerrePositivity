module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentStringPrismChains
public import SerrePositivity.KST.SConstruction.CoherentArrowNativeFamilies

/-! # 同じ元の prism からの共通パラメータ上の二円柱
概要：元の合成列の全精密化を共通パラメータとして、上下の native Hom 評価と実円柱を作る。
方針：同じ長辺の全合成列の収縮を、上下の列の関手に前合成する。
規約：二円柱は同じ長辺の値から始まり、元の列の全高次評価を保持する。
使われ方：元の K の構造射と段の写像の二つの合成を比較する。
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
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 元の射を時刻零から時刻一へ送る、積圏の元の射。 -/
def coherentPrismArrow {x y : I} (f : x ⟶ y) :
    ((x, ULift.up (0 : Fin 2)) : I × ULift.{u} (Fin 2)) ⟶ (y, ULift.up (1 : Fin 2)) :=
  (f, homOfLE (by change (0 : Fin 2) ≤ 1; decide))

/-- 元の射の全合成列を共通パラメータとする、下側の元の native Hom 評価。 -/
def coherentPrismLowerNativeFamily
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶
      SimplicialCategory.sHom (coherentStringVertexObject Q (x, ULift.up 0))
        (coherentStringVertexObject Q (y, ULift.up 1)) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f) ≫ coherentArrowNativeFamily Q (coherentPrismArrow f)

/-- 同じ長辺の値から下側の全合成列の評価へ向かう、共通パラメータ上の実円柱。 -/
def coherentPrismLowerNativeContraction
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex Q (coherentPrismArrow f)))
      (coherentPrismLowerNativeFamily Q f) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (coherentArrowNativeContraction Q (coherentPrismArrow f))
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f))

/-- 下側の円柱は、同じ元の全合成列の円柱の厳密な制限である。 -/
lemma coherentPrismLowerNativeContraction_h
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    (coherentPrismLowerNativeContraction Q f).h =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentArrowNativeContraction Q (coherentPrismArrow f)).h := rfl

/-- 共通パラメータの元の頂点では、下側の同じ全頂点 Path の評価を回収する。 -/
lemma coherentPrismLowerNativeFamily_vertex
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    (coherentPrismLowerNativeFamily Q f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      (coherentStringNativeMap Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s))) := by
  have hv : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s) := by
    refine ComposableArrows.ext₀ ?_
    rfl
  change (coherentArrowNativeFamily Q (coherentPrismArrow f)).app _
    ((nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) = _
  rw [hv]
  exact coherentArrowNativeFamily_vertex Q (coherentPrismArrow f) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString s)

/-- 元の射の全合成列を共通パラメータとする、上側の元の native Hom 評価。 -/
def coherentPrismUpperNativeFamily
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) ⟶
      SimplicialCategory.sHom (coherentStringVertexObject Q (x, ULift.up 0))
        (coherentStringVertexObject Q (y, ULift.up 1)) :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f) ≫ coherentArrowNativeFamily Q (coherentPrismArrow f)

/-- 同じ長辺の値から上側の全合成列の評価へ向かう、共通パラメータ上の実円柱。 -/
def coherentPrismUpperNativeContraction
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    SSet.Homotopy
      (SSet.const (coherentArrowNativeInitialVertex Q (coherentPrismArrow f)))
      (coherentPrismUpperNativeFamily Q f) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (coherentArrowNativeContraction Q (coherentPrismArrow f))
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f))

/-- 上側の円柱は、同じ元の全合成列の円柱の厳密な制限である。 -/
lemma coherentPrismUpperNativeContraction_h
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) :
    (coherentPrismUpperNativeContraction Q f).h =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentArrowNativeContraction Q (coherentPrismArrow f)).h := rfl

/-- 共通パラメータの元の頂点では、上側の同じ全頂点 Path の評価を回収する。 -/
lemma coherentPrismUpperNativeFamily_vertex
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {x y : I} (f : x ⟶ y) (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    (coherentPrismUpperNativeFamily Q f).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) =
      (coherentStringNativeMap Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentStringFullPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s))) := by
  have hv : (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s) := by
    refine ComposableArrows.ext₀ ?_
    rfl
  change (coherentArrowNativeFamily Q (coherentPrismArrow f)).app _
    ((nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex s)) = _
  rw [hv]
  exact coherentArrowNativeFamily_vertex Q (coherentPrismArrow f) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString s)

end SerrePositivity.KST.SConstruction
