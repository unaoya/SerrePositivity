module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentVertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：通常の順序圏上の図式を simplicial thickening 上の豊穣関手へ送る。
方針：順方向の Hom は図式の射に定値とし、逆方向の Hom の空性で構造則を閉じる。
規約：元の単体的圏の通常の射との整合性を用い、局所 Kan 性は不要。
使われ方：coherent nerve 内に指定射の辺と厳密な合成図式を構成する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {J : Type v} [LinearOrder J]

/-- 概要：順序図式の一つの Hom を豊穣 Hom への写像にする。
方針：順方向では元の射の零単体に定値とし、逆方向では空の Hom から写す。
規約：a≤b の証明の違いは通常の順序圏の射の一意性で消える。
使われ方：順序図式の豊穣化の Hom 成分。 -/
def coherentOrderHomMap (F : J ⥤ C) (a b : J) :
    nerve (SimplicialThickening.Path a b) ⟶ SimplicialCategory.sHom (F.obj a) (F.obj b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.orderDiagramEnrichedHom F ⟨a⟩ ⟨b⟩

/-- 概要：通常の順序図式は simplicial thickening からの豊穣関手を与える。
方針：Hom を定値に写し、元の図式の合成則と空の Hom の一意性を使う。
規約：高次の比較は恒等であり、任意の coherent 図式の読み戻しは主張しない。
使われ方：通常の射とその合成を coherent nerve 内で具体化する。 -/
def coherentOrderDiagram (F : J ⥤ C) :
    EnrichedFunctor SSet (SimplicialThickening J) C := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
