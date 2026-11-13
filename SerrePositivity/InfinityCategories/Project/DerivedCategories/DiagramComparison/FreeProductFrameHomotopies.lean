module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductDiagramHomotopies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrameUncurry
public import SerrePositivity.HomologicalAlgebra.CurriedDiagramHomotopy

/-!
概要：全余単体・図式添字で自然な、指定 frame の合成のホモトピー。
方針：積添字上の既存 EZ ホモトピーを恒等成分の同型で運び、添字を戻す。
規約：パラメータごとにホモトピーを選ばない。
使われ方：HA 1.2.4、IS-W2 §73 A02。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u}))
variable (φ : simplicialRingCoefficient.{u} →+* A)
local notation "E" => functorToComplexOfFunctors (SimplexCategory × J) (ModuleCat A) (ComplexShape.up ℤ)
local notation "EE" =>
  (Functor.obj (Functor.whiskeringRight SimplexCategory
    (J ⥤ CochainComplex (ModuleCat A) ℤ) (CochainComplex (J ⥤ ModuleCat A) ℤ))
      (functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)) ⋙
    functorToComplexOfFunctors SimplexCategory (J ⥤ ModuleCat A) (ComplexShape.up ℤ))

/-- 指定 AW・shuffle の合成は、全パラメータの二重図式で恒等射にホモトピック。 -/
def freeProductFrameAWShuffleHomotopy :
    Homotopy ((EE).map (freeProductFrameAW A W P φ ≫ freeProductFrameShuffle A W P φ))
      (𝟙 ((EE).obj (freeProductFrame A W P))) := by
  let e := (E).mapIso (freeProductFrameUncurryIso A W P)
  let h := ((freeProductDiagramAWShuffleHomotopy φ (frameWeightDiagram W)
    (Functor.uncurry.obj P)).compLeft e.hom).compRight e.inv
  apply curriedDiagramHomotopy (.up ℤ)
    (freeProductFrameAW A W P φ ≫ freeProductFrameShuffle A W P φ) (𝟙 _)
  have he : e.hom ≫
      (E).map (freeProductDiagramAW φ (frameWeightDiagram W) (Functor.uncurry.obj P) ≫
        freeProductDiagramShuffle φ (frameWeightDiagram W) (Functor.uncurry.obj P)) ≫
        e.inv =
      (E).map (Functor.uncurry.map
        (freeProductFrameAW A W P φ ≫ freeProductFrameShuffle A W P φ)) := by
    ext i n
    simp [e, freeProductFrameUncurryIso, freeProductFrameAW, freeProductFrameShuffle,
      functorToComplexOfFunctors]
    rfl
  simpa only [Category.assoc, he, Category.id_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id] using h

/-- 指定 shuffle・AW の逆順の合成も、同じ二重図式で恒等射にホモトピック。 -/
def freeProductFrameShuffleAWHomotopy :
    Homotopy ((EE).map (freeProductFrameShuffle A W P φ ≫ freeProductFrameAW A W P φ))
      (𝟙 ((EE).obj (freeTensorFrame A W P))) := by
  let e₀ : Functor.uncurry.obj (freeTensorFrame A W P) ≅
      freeNegativeChainsDiagram (A := A) (frameWeightDiagram W) ⊗
        freeNegativeChainsDiagram (A := A) (Functor.uncurry.obj P) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro x y f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      change (𝟙 (freeNegativeChains (A := A) (W.obj x.2)) ⊗ₘ
        freeNegativeChainsMap (A := A) ((P.map f.1).app x.2)) ≫
        (freeNegativeChainsMap (A := A) (W.map f.2) ⊗ₘ
          freeNegativeChainsMap (A := A) ((P.obj y.1).map f.2)) =
        freeNegativeChainsMap (A := A) (W.map f.2) ⊗ₘ
          freeNegativeChainsMap (A := A)
            ((P.map f.1).app x.2 ≫ (P.obj y.1).map f.2)
      simp only [tensorHom_comp_tensorHom, Category.id_comp, freeNegativeChainsMap,
        ← HomologicalComplex.extendMap_comp, ← CategoryTheory.Functor.map_comp,
        ← Functor.whiskerRight_comp])
  let e := (E).mapIso e₀
  let h := ((freeProductDiagramShuffleAWHomotopy φ (frameWeightDiagram W)
    (Functor.uncurry.obj P)).compLeft e.hom).compRight e.inv
  apply curriedDiagramHomotopy (.up ℤ)
    (freeProductFrameShuffle A W P φ ≫ freeProductFrameAW A W P φ) (𝟙 _)
  have he : e.hom ≫
      (E).map (freeProductDiagramShuffle φ (frameWeightDiagram W) (Functor.uncurry.obj P) ≫
        freeProductDiagramAW φ (frameWeightDiagram W) (Functor.uncurry.obj P)) ≫
        e.inv =
      (E).map (Functor.uncurry.map
        (freeProductFrameShuffle A W P φ ≫ freeProductFrameAW A W P φ)) := by
    ext i n
    simp [e, e₀, freeProductFrameAW, freeProductFrameShuffle, functorToComplexOfFunctors]
    rfl
  simpa only [Category.assoc, he, Category.id_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id] using h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
