module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OrdinaryNatTransPrism

/-!
概要：集合値の重みの射を、区間上の一つの要素の圏にまとめる。
方針：通常の二点図式を uncurry し、始点の要素とその像を結ぶ自然変換を取る。
規約：終点では元の mapElements を使い、ラベルを捨てない。
使われ方：G8 の四角形①における、元の要素の圏からの比較の区間族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 重みの射を、区間と元の添字圏の直積上の集合値図式にする。 -/
def setWeightIntervalDiagram (φ : X ⟶ Y) : (Fin 2 × I) ⥤ Type u :=
  Functor.uncurry.obj (ComposableArrows.mk₁ φ)

/-- 元の始域の要素を、区間上の要素の圏の始点へ入れる。 -/
def setWeightElementsIntervalZero (φ : X ⟶ Y) :
    X.Elements ⥤ (setWeightIntervalDiagram φ).Elements where
  obj e := (setWeightIntervalDiagram φ).elementsMk (0, e.obj) e.val
  map f := ⟨(𝟙 0, f.hom), by simpa [setWeightIntervalDiagram] using f.map_val⟩

/-- 元の終域の要素を、同じ区間上の要素の圏の終点へ入れる。 -/
def setWeightElementsIntervalOne (φ : X ⟶ Y) :
    Y.Elements ⥤ (setWeightIntervalDiagram φ).Elements where
  obj e := (setWeightIntervalDiagram φ).elementsMk (1, e.obj) e.val
  map f := ⟨(𝟙 1, f.hom), by simpa [setWeightIntervalDiagram] using f.map_val⟩

/-- 元の要素からその指定像へ向かう、区間上の要素の圏の自然変換。 -/
def setWeightElementsIntervalTransformation (φ : X ⟶ Y) :
    setWeightElementsIntervalZero φ ⟶ φ.mapElements ⋙ setWeightElementsIntervalOne φ where
  app e := ⟨(homOfLE (by decide : (0 : Fin 2) ≤ 1), 𝟙 e.obj), by
    change Y.map (𝟙 e.obj) (φ.app e.obj e.val) = φ.app e.obj e.val
    simp⟩
  naturality {_ _} f := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp

/-- 要素とその指定像を全単体で結ぶ、元の自然変換の prism。 -/
def setWeightElementsIntervalPrism (φ : X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⊗ nerve X.Elements ⟶ nerve (setWeightIntervalDiagram φ).Elements :=
  ordinaryNatTransPrism (setWeightElementsIntervalTransformation φ)

/-- 区間族の始点は、元の要素の圏の始点への包含である。 -/
lemma setWeightElementsIntervalPrism_zero (φ : X ⟶ Y) :
    prismEndpoint 0 (nerve X.Elements) ≫ setWeightElementsIntervalPrism φ =
      nerveMap (setWeightElementsIntervalZero φ) :=
  ordinaryNatTransPrism_zero _

/-- 区間族の終点は、元の mapElements と終点への包含の合成である。 -/
lemma setWeightElementsIntervalPrism_one (φ : X ⟶ Y) :
    prismEndpoint 1 (nerve X.Elements) ≫ setWeightElementsIntervalPrism φ =
      nerveMap (φ.mapElements ⋙ setWeightElementsIntervalOne φ) :=
  ordinaryNatTransPrism_one _

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
