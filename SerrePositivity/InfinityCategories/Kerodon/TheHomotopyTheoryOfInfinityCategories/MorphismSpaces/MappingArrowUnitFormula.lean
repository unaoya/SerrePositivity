module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowPrefix

/-!
概要：coherent な矢印比較は抽出した単位による合成を表す。
方針：始域固定の伸長を比較で写し、正方形の四辺の合成関係を読む。
規約：各点の比較の同値性も随伴の存在も仮定しない。
使われ方：B1 の自然な写像空間対応から指定単位の局所判定へ進む。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G)

/-- 概要：抽出した単位を任意の始域図式に沿って制限する。
方針：単位の raw なホモトピーに前合成し端点を正規化する。
規約：図式は非定値でよい。使われ方：比較正方形の左辺。 -/
def unitAlong {A : SSet.{u}} (a : A ⟶ X) : SSet.Homotopy a ((a ≫ F) ≫ G) where
  h := (a ▷ (Δ[1] : SSet.{u})) ≫ q.unitHomotopy.h
  h₀ := by rw [SSet.ι₀_comp_assoc, q.unitHomotopy.h₀]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, q.unitHomotopy.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：始域固定の伸長を coherent な比較で写したホモトピー。
方針：矢印空間内の伸長に比較を後合成する。
規約：同じ族全体を写す。使われ方：単位による合成を読む正方形。 -/
def prefixComparison {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    SSet.Homotopy ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F) ≫ q.map)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F a b H ≫ q.map) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefixPath F a b H) q.map

/-- 概要：比較正方形の下辺は始域図式に定値。
方針：比較が始域射影を保つことと伸長の始域固定を使う。
規約：raw な下辺の回収。使われ方：正方形の合成関係の恒等辺。 -/
lemma prefixSquare_bottom {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare (q.prefixComparison a b H) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_bottom]
  change curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefix F a b H ≫ q.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) = _
  rw [q.source, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefix_source]
  apply uncurry_injective
  rw [uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 概要：比較正方形の上辺は元の矢印の G による像。
方針：比較が標的射影を保つことと伸長の標的回収を使う。
規約：同じ H の後合成。使われ方：単位の後に合成する射。 -/
lemma prefixSquare_top {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare (q.prefixComparison a b H) =
      curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H G).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_top]
  change curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefix F a b H ≫ q.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G ≫ G) = _
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefix F a b H ≫ q.map) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = H.h := by
    rw [Category.assoc, q.target, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowPrefix_target]
  rw [← Category.assoc, ht]
  rfl

/-- 概要：比較正方形の左辺は抽出した単位の制限。
方針：恒等矢印の族の像とパラメータ前合成自然性を使う。
規約：単位の代表を選び直さない。使われ方：合成公式の単位の因子。 -/
lemma prefixSquare_left {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare (q.prefixComparison a b H) =
      curry (q.unitAlong a).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_left]
  apply congrArg curry
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy ((a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowIdentityFamily F) ≫ q.map)).h = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp a q.unitDiagram

/-- 概要：比較正方形の右辺は元の矢印の比較の像。
方針：伸長の終点を回収する。
規約：raw な代表の等式。使われ方：合成公式の結論。 -/
lemma prefixSquare_right {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare (q.prefixComparison a b H) =
      curry (q.mapHomotopy a b H).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare_right (q.prefixComparison a b H)

/-- 概要：coherent な矢印比較は抽出単位と G による後合成の合成を表す。
方針：伸長の像の正方形の四辺から h Fun の合成関係を得る。
規約：非定値の端点・任意の単体集合パラメータを許す。
使われ方：自然な比較の各点での同値性を指定単位版へ接続する。 -/
lemma mapHomotopy_hom {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ F) b) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (q.mapHomotopy a b H)) =
      (hoFunctor.map ((pre a).app X)).toFunctor.map q.unitHom ≫
        (hoFunctor.map ((ihom A).map G)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHom_comp_eq_of_square (q.unitAlong a) (q.mapHomotopy a b H)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H G) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopySquare (q.prefixComparison a b H))
    (q.prefixSquare_bottom a b H) (q.prefixSquare_top a b H)
    (q.prefixSquare_left a b H) (q.prefixSquare_right a b H)
  have hu : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (q.unitAlong a)) =
        (hoFunctor.map ((pre a).app X)).toFunctor.map q.unitHom :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom q.unitHomotopy a
  rw [hu, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] at hs
  exact hs.symm

end MappingArrowComparison
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
