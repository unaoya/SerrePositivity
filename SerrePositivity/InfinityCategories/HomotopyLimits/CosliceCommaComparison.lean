module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1B.UnitCommaFiberExtension
public import SerrePositivity.InfinityCategories.F1B.KanUnitCommaFiberIntervalIso
public import SerrePositivity.InfinityCategories.F1B.VertexFiberBaseChange

/-!
概要：join 型の coslice の底変換から、始点固定の区間型 comma への標準比較。
方針：元の join の普遍族を左の円筒比較で制限し、標的図式を保って curry する。
規約：元の辺・底の図式・全単体集合パラメータを保持。
使われ方：局所対象への普遍矢印から反射の構成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 底変換した元の coslice の普遍族を、始点固定・標的可変の区間族として読む。 -/
def cosliceCommaHomotopy {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    SSet.Homotopy (SSet.const x)
      (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G ≫ G) where
  h := (β_ _ (Δ[1] : SSet.{u})).hom ≫ leftMappingSpacePrism _ ≫
    sliceUnderUncurry (pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)
  h₀ := by
    change prismEndpoint 0 _ ≫ (leftMappingSpacePrism _ ≫ sliceUnderUncurry _) = _
    rw [← Category.assoc, leftMappingSpacePrism_zero, Category.assoc,
      sliceUnderUncurry_fixed, const_point_comp_yoneda]
    rfl
  h₁ := by
    change prismEndpoint 1 _ ≫ (leftMappingSpacePrism _ ≫ sliceUnderUncurry _) = _
    rw [← Category.assoc, leftMappingSpacePrism_one, sliceUnderUncurry_projection,
      pullback.condition]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 元の coslice を底変換した全空間から、固定始点の comma への実際の標準射。 -/
def cosliceCommaComparison {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    pullback (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G ⟶ unitCommaFiber G x :=
  unitCommaFiberCurry G x (pullback.snd _ _) (cosliceCommaHomotopy G x)

/-- 標準比較は元の標的図式を厳密に保持する。 -/
lemma cosliceCommaComparison_projection {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    cosliceCommaComparison G x ≫ F1B.kanUnitCommaFiberProjection G x =
      pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G :=
  unitCommaFiberCurry_target G x _ _

/-- 標準比較の任意の族の展開は、元の join の族への左円筒の制限。 -/
lemma cosliceCommaComparison_uncurry {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (s : A ⟶ pullback (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) :
    unitCommaUncurry ((s ≫ cosliceCommaComparison G x) ≫ vertexFiberι (unitCommaSource G) x) =
      leftMappingSpacePrism A ≫ sliceUnderUncurry
        (s ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) := by
  rw [Category.assoc, unitCommaUncurry_precomp]
  unfold cosliceCommaComparison
  rw [unitCommaFiberCurry_uncurry]
  dsimp only [cosliceCommaHomotopy]
  rw [← Category.assoc (β_ (Δ[1] : SSet.{u}) _).hom,
    SymmetricCategory.symmetry, Category.id_comp, ← Category.assoc,
    leftMappingSpacePrism_naturality, Category.assoc, sliceUnderUncurry_precomp]

end SerrePositivity.InfinityCategories.HomotopyLimits
