module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaUnitComponent

/-!
概要：標準単位比較を元の単位の代表との合成三角形で実現する。
方針：写像空間全体をパラメータとし、前合成の h Fun の公式から三辺固定の三角形を選ぶ。
規約：比較の同値性は仮定しない。選ぶのは普遍パラメータ上の三角形一つ。
使われ方：導来 fiber の path を取り込む前の基準合成図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単位比較の普遍族は単位成分と G による普遍標的辺の合成を表す。
方針：comma の単位成分の認識と区間の前合成の公式を合わせる。
規約：元の単位のホモトピー代表を保持する。
使われ方：実際の合成三角形の存在判定。 -/
lemma unitIntervalMap_composition_hom {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (unitCommaSectionVertexHomotopy
        (A := intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) η x)) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (intervalFamilyHomotopy (intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y))) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (intervalFamilyHomotopy (unitIntervalMap η x y))) := by
  rw [unitCommaSectionVertexHomotopy_hom]
  change _ ≫ intervalFamilyHom _ = intervalFamilyHom _
  rw [unitIntervalMap, intervalPrecompose_family]

/-- 概要：標準単位比較の普遍族の指定三辺を持つ合成三角形。
方針：関手単体集合内の合成の等式から、三辺の代表を保った実際の二単体を選ぶ。
規約：パラメータは Map(F(x),y) 全体で、単位比較の同値性は不要。
使われ方：任意の族へ前合成して、逆向きの比較の基準三角形を得る。 -/
noncomputable def unitIntervalCompositionTriangle {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    FunctorCompositionTriangle
      (unitCommaSectionVertexHomotopy
        (A := intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) η x)
      (intervalFamilyHomotopy (intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y))
      (intervalFamilyHomotopy (unitIntervalMap η x y)) :=
  (nonempty_functorCompositionTriangle_of_homEq _ _ _ (unitIntervalMap_composition_hom η x y)).some

/-- 概要：区間族のホモトピー表示はパラメータ前合成に自然。
方針：展開の自然性と区間交換の自然性を組み合わせる。
規約：始域・標的に quasicategory 性を課さない。
使われ方：基準三角形の三辺を族へ制限する際の厳密な式。 -/
lemma intervalFamilyHomotopy_precomp_h {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    (intervalFamilyHomotopy (i ≫ f)).h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (intervalFamilyHomotopy f).h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry (i ≫ f) =
    (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ B (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry f
  rw [intervalMappingUncurry_precomp]
  have hb : (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] : SSet.{u}) ◁ i =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ B (Δ[1] : SSet.{u})).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  rw [← Category.assoc, hb, Category.assoc]

/-- 概要：普遍単位三角形を任意の写像空間の族へ制限した合成三角形。
方針：基準三角形への前合成と三辺の raw な自然性を用いる。
規約：族ごとに独立な合成三角形を選び直さない。
使われ方：導来 fiber の普遍標的族に対する基準合成を用意する。 -/
noncomputable def unitIntervalCompositionTriangle_family {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    FunctorCompositionTriangle (unitCommaSectionVertexHomotopy (A := A) η x)
      (intervalFamilyHomotopy (f ≫ intervalFunctorMap G (F.app (Opposite.op ⦋0⦌) x) y))
      (intervalFamilyHomotopy (f ≫ unitIntervalMap η x y)) :=
  (unitIntervalCompositionTriangle η x y).precomp f _ _ _
    (by
      change (unitCommaFiberHomotopy (SSet.const (unitCommaSectionVertex η x) :
        A ⟶ unitCommaFiber G x)).h =
          (f ▷ (Δ[1] : SSet.{u})) ≫
            (unitCommaFiberHomotopy (SSet.const (unitCommaSectionVertex η x))).h
      rw [unitCommaSectionVertex_homotopy_const, unitCommaSectionVertex_homotopy_const,
        ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, SSet.comp_const])
    (intervalFamilyHomotopy_precomp_h f _) (intervalFamilyHomotopy_precomp_h f _)

/-- 概要：族の合成三角形の図式は選んだ普遍三角形の制限そのもの。
方針：前合成による三角形の定義を読む。
規約：厳密な等式。
使われ方：逆向きの構成のパラメータ整合性の検証。 -/
lemma unitIntervalCompositionTriangle_family_diagram {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y) :
    (unitIntervalCompositionTriangle_family η x y f).diagram =
      (unitIntervalCompositionTriangle η x y).diagram ≫ (pre f).app X := rfl

end SerrePositivity.InfinityCategories
