module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberIntervalIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange

/-!
概要：coslice による局所添字を固定始域の comma の fiber へ写す。
方針：普遍錐を左の円柱で展開し、区間の指定変換として comma へ持ち上げる。
規約：比較射の定義に quasicategory 性は不要。
使われ方：反転前の局所 Kan 添字を写像空間の比較に還元する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：一点からの coslice の図式は固定始点から射影への指定変換を与える。
方針：普遍錐を左の円柱比較で展開する。
規約：時間はホモトピーの第二因子。
使われ方：coslice の図式を interval comma に束ねる。 -/
def kanPointCosliceHomotopy {A X : SSet.{u}} (x : X _⦋0⦌)
    (a : A ⟶ sliceUnder (SSet.yonedaEquiv.symm x)) :
    SSet.Homotopy (SSet.const x) (a ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x)) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ leftMappingSpacePrism A ≫ sliceUnderUncurry a
  h₀ := by
    change prismEndpoint 0 A ≫ leftMappingSpacePrism A ≫ sliceUnderUncurry a = _
    rw [← Category.assoc, leftMappingSpacePrism_zero, Category.assoc, sliceUnderUncurry_fixed,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    rfl
  h₁ := by
    change prismEndpoint 1 A ≫ leftMappingSpacePrism A ≫ sliceUnderUncurry a = _
    rw [← Category.assoc, leftMappingSpacePrism_one, sliceUnderUncurry_projection]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：右 Kan の局所添字上の標準変換。
方針：coslice の射影を pullback の可換条件で元の添字への射影に置き換える。
規約：関手 G は任意。
使われ方：固定始域の comma への持ち上げの端点。 -/
def kanRightKanShapeHomotopy {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    SSet.Homotopy (SSet.const x) (rightKanProjection G x ≫ G) where
  h := (kanPointCosliceHomotopy x (pullback.fst
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)).h
  h₀ := (kanPointCosliceHomotopy x (pullback.fst
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)).h₀
  h₁ := by
    rw [(kanPointCosliceHomotopy x (pullback.fst
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)).h₁]
    exact pullback.condition
  rel := (kanPointCosliceHomotopy x (pullback.fst
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)).rel

/-- 概要：右 Kan の局所添字を始域固定の comma へ写す。
方針：標準変換を comma の普遍性に渡す。
規約：同値性は fiber の比較で後に証明する。
使われ方：通常の局所添字と区間模型の比較。 -/
def kanRightKanShapeToUnitCommaFiber {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌) :
    rightKanShape G x ⟶ unitCommaFiber G x :=
  unitCommaFiberCurry G x (rightKanProjection G x) (kanRightKanShapeHomotopy G x)

/-- 概要：右 Kan の局所比較は Y への射影を保つ。
方針：comma の族の標的の計算則。
規約：射の厳密な等式。
使われ方：同じ底 Y 上の left fibrations の比較。 -/
lemma kanRightKanShapeToUnitCommaFiber_projection {X Y : SSet.{u}}
    (G : Y ⟶ X) (x : X _⦋0⦌) :
    kanRightKanShapeToUnitCommaFiber G x ≫ SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x =
      rightKanProjection G x := unitCommaFiberCurry_target _ _ _ _

/-- 概要：比較後の区間展開は coslice の図式を左の円柱で引き戻した族。
方針：comma の curry の逆則、円柱と coslice のパラメータ自然性を使う。
規約：比較を任意のパラメータから前合成した形を扱う。
使われ方：各 fiber での比較を既存の写像空間比較と同定する。 -/
lemma kanRightKanShapeToUnitCommaFiber_uncurry {A X Y : SSet.{u}}
    (G : Y ⟶ X) (x : X _⦋0⦌) (f : A ⟶ rightKanShape G x) :
    unitCommaUncurry (f ≫ kanRightKanShapeToUnitCommaFiber G x ≫
      vertexFiberι (unitCommaSource G) x) =
        leftMappingSpacePrism A ≫ sliceUnderUncurry
          (f ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) := by
  rw [unitCommaUncurry_precomp]
  dsimp only [kanRightKanShapeToUnitCommaFiber]
  rw [unitCommaFiberCurry_uncurry]
  change (Δ[1] ◁ f) ≫ (β_ (Δ[1] : SSet.{u}) _).hom ≫
    (β_ _ (Δ[1] : SSet.{u})).hom ≫ leftMappingSpacePrism _ ≫ _ = _
  rw [← Category.assoc (β_ (Δ[1] : SSet.{u}) _).hom,
    SymmetricCategory.symmetry, Category.id_comp, ← Category.assoc,
    leftMappingSpacePrism_naturality, Category.assoc, ← sliceUnderUncurry_precomp]

end SerrePositivity.InfinityCategories.F1B
