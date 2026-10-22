module
public import SerrePositivity.InfinityCategories.Stable.LoopConeUniversalSourceInitial
public import SerrePositivity.InfinityCategories.Stable.LoopConeZeroCornerDiagram

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalZeroCornerPoint_isInitial {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X] (s : X ⟶ loopDiagrams X)
    (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    {y : X _⦋0⦌} (t : LoopSquare y) :
    let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))
    IsInitialVertex ((loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
        (loopConeUniversalFixedApexPoint t))) := by
  let p := pullbackCospan t.square
  let c := (sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (pullbackCone t.square)
  let x := (HomotopyLimits.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let e := (loopConeZeroCornerSourceFiberMap_isQCatEquivalence X x).choose
  exact e.map_isInitialVertex (loopConeUniversalSourcePoint_isInitial s hs hΩ t)


/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeUniversalZeroCornerPoint_square {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) :
    let x := (HomotopyLimits.coneFamilyApex (pullbackCospan t.square)).app
      (Opposite.op ⦋0⦌) ((sliceConeFamilyMap (pullbackCospan t.square)).app
        (Opposite.op ⦋0⦌) (pullbackCone t.square))
    ((loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌)
        (loopConeUniversalFixedApexPoint t))).val.val = functorVertex t.square := by
  let p := pullbackCospan t.square
  let c := (sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (pullbackCone t.square)
  let x := (HomotopyLimits.coneFamilyApex p).app (Opposite.op ⦋0⦌) c
  let v := loopConeUniversalFixedApexPoint t
  let Z := (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsZeroCornerSquareVertex).ι
  have hh : (loopConeFixedApexSourceLift t x ≫ loopConeZeroCornerSourceFiberMap X x) ≫
      vertexFiberι (zeroCornerSquareSource X) x ≫ Z =
      HomotopyLimits.fixedApexConeFamilyEvaluation p x ≫ (squareConeFunctorIso X).inv := by
    dsimp only [Z]
    simp only [Category.assoc, loopConeZeroCornerSourceFiberMap,
      reassoc_of% vertexFiberMap_ι, reassoc_of% loopConeFixedApexSourceLift_ι,
      loopConeZeroCornerForget_diagram, reassoc_of% loopConeFixedApexLift_diagram]
    rfl
  have hv : (HomotopyLimits.fixedApexConeFamilyEvaluation p x).app (Opposite.op ⦋0⦌) v =
      functorVertex (pullbackCone t.square).val := by
    change ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) (pullbackCone t.square)).val = _
    rw [sliceConeFamilyMap_app_zero]
    rfl
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app hh (Opposite.op ⦋0⦌)) v
  change ((loopConeZeroCornerSourceFiberMap X x).app (Opposite.op ⦋0⦌)
      ((loopConeFixedApexSourceLift t x).app (Opposite.op ⦋0⦌) v)).val.val =
      (squareConeFunctorIso X).inv.app (Opposite.op ⦋0⦌)
        ((HomotopyLimits.fixedApexConeFamilyEvaluation p x).app (Opposite.op ⦋0⦌) v) at he
  rw [hv] at he
  refine he.trans ?_
  change functorVertex (cospanConeSquareIso.inv ≫ cospanConeSquareIso.hom ≫ t.square) = _
  rw [Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories
