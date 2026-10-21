module

public import SerrePositivity.InfinityCategories.F1B.UnitCompositionTriangle
public import SerrePositivity.InfinityCategories.F1B.CommaSquareUncurry
public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberIntervalIso

/-!
概要：標準単位比較の合成三角形を、固定始域 comma 内の実際の輸送円柱にする。
方針：三角形を正方形へ補完し、元の単位辺を始点として comma の族へ戻す。
規約：指定単位の同じ代表と元の合成三角形を使用。使われ方：始対象からの普遍輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 普遍合成正方形を、非定値の標的辺上で始域 x を固定したホモトピーとして読む。 -/
def unitCommaCompositionCoherence (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    SSet.Homotopy
      (SSet.const x : (Δ[1] : SSet.{u}) ⊗
        intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶ X)
      (intervalMappingUncurry (𝟙 (intervalMappingSpace
        (F.app (Opposite.op ⦋0⦌) x) y)) ≫ G) where
  h := (functorSquareCoherence
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle η x y))).h
  h₀ := (functorSquareCoherence
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle η x y))).h₀
  h₁ := by
    have h := (functorSquareCoherence
      (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle η x y))).h₁
    change SSet.ι₁ ≫ _ = _ at h ⊢
    apply h.trans
    change (β_ (Δ[1] : SSet.{u}) _).hom ≫
      ((β_ _ (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
        (intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y)) = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    change intervalMappingUncurry (intervalFunctorMap G _ _) =
      intervalMappingUncurry (𝟙 _) ≫ G
    simpa only [Category.id_comp] using intervalFunctorMap_uncurry
      (𝟙 (intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)) G
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 単位の元の普遍合成三角形が与える、底の全区間辺を覆う comma 内の円柱。 -/
def unitCommaCompositionPrism (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      unitCommaFiber G x :=
  unitCommaFiberCurry G x (intervalMappingUncurry (𝟙 _))
    (unitCommaCompositionCoherence η x y)

/-- 円柱は元の Y 内の普遍区間辺全体を厳密に覆う。 -/
lemma unitCommaCompositionPrism_projection (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitCommaCompositionPrism η x y ≫ F1B.kanUnitCommaFiberProjection G x =
      intervalMappingUncurry (𝟙 (intervalMappingSpace
        (F.app (Opposite.op ⦋0⦌) x) y)) :=
  unitCommaFiberCurry_target _ _ _ _

/-- 円柱の始点は、元の指定単位の comma 頂点に定値。 -/
lemma unitCommaCompositionPrism_zero (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    prismEndpoint 0 (intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) ≫
      unitCommaCompositionPrism η x y = SSet.const (unitCommaSectionVertex η x) := by
  dsimp only [unitCommaCompositionPrism]
  apply unitCommaFiber_hom_ext
  · rw [unitCommaFiberTarget_precomp, unitCommaFiberCurry_target,
      intervalFamily_zero, unitCommaSectionVertex_target_const]
  · rw [unitCommaFiberHomotopy_precomp, unitCommaFiberCurry_homotopy]
    exact functorSquareCoherence_left
      (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle η x y))

end SerrePositivity.InfinityCategories.HomotopyLimits
