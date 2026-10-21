module

public import SerrePositivity.InfinityCategories.HomotopyLimits.KanTensorEnriched
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：空間の ∞ 圏の二項直積と、元の二射影の coherent な比較を構成する。
方針：Hom の直積を使う豊穣圏の nerve の積同型を介し、両変数の豊穣作用を移す。
規約：射影は全高次で自然な同じ fst・snd から構成。使われ方：点ごとの coherent 積図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 空間の coherent nerve 上で、元の Kan 複体の直積を両変数で取る ∞ 関手。 -/
def spaceTensorProduct : SpaceInfinity.{u} ⊗ SpaceInfinity.{u} ⟶ SpaceInfinity.{u} :=
  simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫ coherentNerveMap kanTensorEnriched

/-- 積の nerve の逆同型は第一射影を厳密に保持する。 -/
lemma spacePairNerveFrom_fst :
    simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
      coherentNerveMap (simplicialPairFst KanObject.{u} KanObject.{u}) =
        fst SpaceInfinity.{u} SpaceInfinity.{u} := by
  change _ = fst (SimplicialNerve KanObject.{u}) (SimplicialNerve KanObject.{u})
  calc
    _ = simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
        (simplicialPairNerveTo KanObject.{u} KanObject.{u} ≫ fst _ _) := by
      rw [simplicialPairNerveTo, lift_fst]
    _ = _ := by
      rw [← Category.assoc,
        show simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
          simplicialPairNerveTo KanObject.{u} KanObject.{u} = 𝟙 _ from
            (simplicialPairNerveIso KanObject.{u} KanObject.{u}).inv_hom_id,
        Category.id_comp]

/-- 積の nerve の逆同型は第二射影も厳密に保持する。 -/
lemma spacePairNerveFrom_snd :
    simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
      coherentNerveMap (simplicialPairSnd KanObject.{u} KanObject.{u}) =
        snd SpaceInfinity.{u} SpaceInfinity.{u} := by
  change _ = snd (SimplicialNerve KanObject.{u}) (SimplicialNerve KanObject.{u})
  calc
    _ = simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
        (simplicialPairNerveTo KanObject.{u} KanObject.{u} ≫ snd _ _) := by
      rw [simplicialPairNerveTo, lift_snd]
    _ = _ := by
      rw [← Category.assoc,
        show simplicialPairNerveFrom KanObject.{u} KanObject.{u} ≫
          simplicialPairNerveTo KanObject.{u} KanObject.{u} = 𝟙 _ from
            (simplicialPairNerveIso KanObject.{u} KanObject.{u}).inv_hom_id,
        Category.id_comp]

/-- 元の fst の全高次の自然性による、二項積から第一因子への coherent な変換。 -/
def spaceTensorProductFstHomotopy :
    SSet.Homotopy spaceTensorProduct (fst SpaceInfinity.{u} SpaceInfinity.{u}) := by
  let H := simplicialHomotopyOfFunctorEdge
    (kanEnrichedComparisonEdge kanTensorEnrichedFst).toTruncated
  let T := functorHomotopyPrecomp H (simplicialPairNerveFrom KanObject.{u} KanObject.{u})
  exact { h := T.h, h₀ := T.h₀, h₁ := T.h₁.trans spacePairNerveFrom_fst, rel := T.rel }

/-- 元の snd の同じ全高次の自然性による、二項積から第二因子への coherent な変換。 -/
def spaceTensorProductSndHomotopy :
    SSet.Homotopy spaceTensorProduct (snd SpaceInfinity.{u} SpaceInfinity.{u}) := by
  let H := simplicialHomotopyOfFunctorEdge
    (kanEnrichedComparisonEdge kanTensorEnrichedSnd).toTruncated
  let T := functorHomotopyPrecomp H (simplicialPairNerveFrom KanObject.{u} KanObject.{u})
  exact { h := T.h, h₀ := T.h₀, h₁ := T.h₁.trans spacePairNerveFrom_snd, rel := T.rel }

/-- 二項積の ∞ 関手の値は、元の Kan 複体の直積の指定頂点そのもの。 -/
lemma spaceTensorProduct_vertex (K L : KanObject.{u}) :
    spaceTensorProduct.app (Opposite.op ⦋0⦌) (coherentNerveVertex K, coherentNerveVertex L) =
      coherentNerveVertex ((kanTensorLeft K).obj L) := by
  change (coherentNerveMap kanTensorEnriched).app _
    ((simplicialPairNerveFrom KanObject.{u} KanObject.{u}).app _
      (coherentNerveVertex K, coherentNerveVertex L)) = _
  rw [simplicialPairNerveFrom_vertex, coherentNerveMap_vertex]
  rfl

/-- 任意の coherent な二図式に同じ二項積の ∞ 関手を後合成する。 -/
def coherentSpaceTensorProduct {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) : B ⟶ SpaceInfinity.{u} :=
  lift F G ≫ spaceTensorProduct

/-- 点ごとの積図式の値は、二つの元の値の Kan 複体の直積。 -/
lemma coherentSpaceTensorProduct_vertex {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (coherentSpaceTensorProduct F G).app (Opposite.op ⦋0⦌) b =
      coherentNerveVertex ((kanTensorLeft (spaceInfinityObject (F.app _ b))).obj
        (spaceInfinityObject (G.app _ b))) := by
  change spaceTensorProduct.app (Opposite.op ⦋0⦌) (F.app _ b, G.app _ b) = _
  have h := spaceTensorProduct_vertex
    (spaceInfinityObject (F.app _ b)) (spaceInfinityObject (G.app _ b))
  simpa only [spaceInfinityObject, coherentNerveVertex_object] using h

end SerrePositivity.InfinityCategories.HomotopyLimits
