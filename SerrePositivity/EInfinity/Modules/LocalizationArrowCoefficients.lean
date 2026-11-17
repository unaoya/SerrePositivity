module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.Modules.FreeHammockCoefficientNerve
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.SourceHom
public import SerrePositivity.EInfinity.Hammock.RelativeFixedArrow

/-!
# 同じ局所化の係数作用による指定生成射の保存

概要：HTT Definition 1.1.5.5 の同じ nerve 作用で、元の通常射の辺を保つ。
方針：自由解像の零次の一文字の射から、同じ左右比較・Kan 化・nerve へ移す。
規約：元の射・端点を保持し、別の局所化辺を選ばない。
使われ方：HA §4.2.3 の BE 加群族における指定弱辺との照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory Opposite SSet
open SerrePositivity.EInfinity _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open scoped Simplicial
variable {C D : RelativeCategory.{u}} (F : C ⟶ D) {X Y : C.category}

/-- 概要：同じ零次の一文字の射を元の係数関手で移す（HTT §1.1.5）。
方針：同じ自由圏の係数関手と端点の等式の合成を計算する。
規約：元の自由な生成射。使われ方：同じ自由 hammock の辺の保存。 -/
lemma freeResolutionArrowZero_coefficient (f : X ⟶ Y) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F (op ⦋0⦌) X).symm ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app (op ⦋0⦌)).functor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F (op ⦋0⦌) Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero D (F.functor.map f) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  change eqToHom _ ≫ (Cat.freeMap F.functor.toPrefunctor).map ((Paths.of C.category).map f) ≫
    eqToHom _ = eqToHom _ ≫ (Paths.of D.category).map (F.functor.map f) ≫ eqToHom _
  simp only [Cat.freeMap_map, Paths.of_map, Prefunctor.mapPath_toPath]
  rfl

/-- 概要：同じ自由 hammock の元の零単体は係数作用で同じ射へ移る（HTT §1.1.5）。
方針：固定端点の一列の保存と同じ零次の計算を使う。
規約：元の両端点。使われ方：単位からの指定点の保存。 -/
lemma freeHammockArrowZero_coefficient (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y).app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowZero C f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowZero D (F.functor.map f) := by
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockMap F X Y).app (op ⦋0⦌)).app (op ⦋0⦌)
    (arrowPoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj (op ⦋0⦌)).weakEquivalences
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) (op ⦋0⦌)) = _
  rw [freeHammockCoefficient_fixedColimitMap]
  have h := Hammock.Relative.fixedColimitMap_arrowPoint ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap F).app (op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F (op ⦋0⦌) X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMap_object F (op ⦋0⦌) Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionArrowZero C f) (op ⦋0⦌)
  rw [freeResolutionArrowZero_coefficient] at h
  exact h

/-- 概要：同じ自由 hammock の指定点は係数作用で保存される（HTT §1.1.5）。
方針：元の零単体と単位からの写像の標準同値を使う。
規約：単体写像の等式。使われ方：Kan 化した指定射の保存。 -/
lemma freeHammockArrowPoint_coefficient (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint D (F.functor.map f) := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.unitPointMap_comp, freeHammockArrowZero_coefficient]
  rfl

/-- 概要：同じ自由局所化の指定点は係数作用で保存される（HTT §1.1.5）。
方針：元の自由 hammock の点と同じ比較の自然性を貼る。
規約：元の localizationHomMap。使われ方：指定された DK 射の保存。 -/
lemma localizationArrowPoint_coefficient (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint D (F.functor.map f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint_comparison C f, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap_comparison, ← Category.assoc,
    freeHammockArrowPoint_coefficient, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint_comparison]

/-- 概要：同じ Kan 局所化の指定射は係数作用で保存される（HTT §1.1.5）。
方針：指定点の保存を同じ Ex∞ の単位の自然性で移す。
規約：同じ通常化された豊穣圏の射。使われ方：native 辺の保存。 -/
lemma kanLocalizationStrictHom_coefficient (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationFunctor F).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom D (F.functor.map f) := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom]
  change ForgetEnrichment.homOf SSet (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanLocalizationObjects D)
    (X := F.functor.obj X) (Y := F.functor.obj Y)
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationArrowPoint C f ≫ exInfinityUnit.app _) ≫
      exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomMap F X Y)) = _
  rw [Category.assoc, ← exInfinityUnit.naturality, Functor.id_map,
    ← Category.assoc, localizationArrowPoint_coefficient]
  rfl

/-- 概要：同じ Kan 自由 hammock の指定射は係数作用で保存される（HTT §1.1.5）。
方針：元の指定点と同じ Ex∞ 単位を使う。
規約：同じ自由 hammock の射。使われ方：元の左右比較の辺の照合。 -/
lemma kanFreeHammockStrictHom_coefficient (f : X ⟶ Y) :
    (kanFreeHammockCoefficientFunctor F).forget.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom D (F.functor.map f) := by
  simp only [EnrichedFunctor.forget_map, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom, ForgetEnrichment.homTo_homOf]
  change ForgetEnrichment.homOf SSet (C := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanFreeHammockObjects D)
    (X := F.functor.obj X) (Y := F.functor.obj Y)
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockArrowPoint C f ≫ exInfinityUnit.app _) ≫
      exInfinity.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalMap F X Y)) = _
  rw [Category.assoc, ← exInfinityUnit.naturality, Functor.id_map,
    ← Category.assoc, freeHammockArrowPoint_coefficient]
  rfl

/-- 概要：同じ局所化の実辺は全係数作用で保存される（HTT Definition 1.1.5.5）。
方針：豊穣射の保存を同じ coherent nerve の辺に適用する。
規約：実際の一単体の等式。使われ方：指定弱辺と全自然性の照合。 -/
lemma localizationStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f)).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap F)).edge =
      (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom D (F.functor.map f))).edge := by
  exact coherentNerveMap_edge_of_homEquiv (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationEnrichedMap F)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom C f) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanLocalizationStrictHom D (F.functor.map f))
    (by rw [← kanLocalizationStrictHom_coefficient F f]; rfl)

/-- 概要：同じ自由 hammock の実辺も全係数作用で保存される（HTT Definition 1.1.5.5）。
方針：同じ自由 hammock の豊穣射の保存を nerve へ移す。
規約：実際の一単体の等式。使われ方：元の比較二胞体の成分への接続。 -/
lemma freeHammockStrictEdge_coefficient (f : X ⟶ Y) :
    ((coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f)).map
      (kanFreeHammockCoefficientNerve F)).edge =
      (coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom D (F.functor.map f))).edge := by
  exact coherentNerveMap_edge_of_homEquiv (kanFreeHammockCoefficientFunctor F)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom C f) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanFreeHammockStrictHom D (F.functor.map f))
    (by rw [← kanFreeHammockStrictHom_coefficient F f]; rfl)

attribute [cite HTT "1.1.5.5" (partial := component)
  "同じ局所化の係数作用が元の指定生成射を保つ照合。一般の局所化の普遍性は含まない。"]
  freeResolutionArrowZero_coefficient freeHammockArrowZero_coefficient
  freeHammockArrowPoint_coefficient localizationArrowPoint_coefficient
  kanLocalizationStrictHom_coefficient kanFreeHammockStrictHom_coefficient
  localizationStrictEdge_coefficient freeHammockStrictEdge_coefficient

end SerrePositivity.EInfinity.Modules
