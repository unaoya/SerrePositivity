module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyRelativePost

/-!
概要：元の定値標的作用の後の指定比較の値を、標的頂点の表示変更で保持する。
方針：頂点等式を消去し、同じ実円柱の外延性を使う。
規約：実円柱と比較を選び直さない。使われ方：元の単位円柱と native 単位表現の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ定値標的への円柱の表示変更は、その作用後の指定比較の同じ値を保つ。 -/
lemma functorHomotopyConstantPost_value_heq_target {B C : SSet.{u + 1}}
    {J : B ⟶ SpaceInfinity.{u}} {z z' : SpaceInfinity.{u} _⦋0⦌}
    (H : SSet.Homotopy J (SSet.const z)) (H' : SSet.Homotopy J (SSet.const z'))
    (hz : z = z') (hh : H.h = H'.h) (p : C ⟶ B)
    {x y : (relativeFunctorSpace (leftUnstraighteningProjection J) p) _⦋0⦌}
    (e : VertexIso x y) :
    HEq (VertexIso.map (VertexIso.map e (functorHomotopyRelativePost H p))
      ((constantUnstraighteningRelativeIso p z).hom ≫
        (ihom C).map (pointedSpaceFiberValueEquivalence z).hom))
      (VertexIso.map (VertexIso.map e (functorHomotopyRelativePost H' p))
        ((constantUnstraighteningRelativeIso p z').hom ≫
          (ihom C).map (pointedSpaceFiberValueEquivalence z').hom)) := by
  subst z'
  have hH : H = H' := SSet.RelativeMorphism.Homotopy.ext hh
  subst H'
  rfl

end SerrePositivity.InfinityCategories.F2
