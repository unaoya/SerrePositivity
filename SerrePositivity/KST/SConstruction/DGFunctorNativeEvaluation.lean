module
public import SerrePositivity.KST.SConstruction.DGFunctorTensorEvaluation
public import SerrePositivity.KST.SConstruction.DGNativePointSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：全次数 dg 関手 end の native 全単体を、元 dg nerve 間の全関手族に評価する。
方針：Serre 対角の tensor 比較を同時評価へ写し、内部 Hom へ転置する。
規約：core への制限なし。標的の Small 仮定なし。元の固定関手を厳密回収する。
使われ方：元 cone の全 end 二単体を全関手族の指定零化面へ運ぶ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Opposite SSet
open DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [DGCategory R E]

/-- 概要：元対象と全 native dg 関手族の実単体的同時評価。
方針：各次数で元 tensor 単体を同じ厳密評価へ写す。
規約：全高次・非可逆入力を保持。使われ方：全関手族への転置。 -/
def dgFunctorNativeEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E where
  app _ := ↾fun p => (dgNerveTensorSimplex R p.1 p.2).map (dgFunctorTensorEvaluation R D E)
  naturality X Y f := by
    ext p
    change (dgNerveTensorSimplex R (p.1.pullback f.unop.toOrderHom)
        (p.2.pullback f.unop.toOrderHom)).map (dgFunctorTensorEvaluation R D E) =
      ((dgNerveTensorSimplex R p.1 p.2).map (dgFunctorTensorEvaluation R D E)).pullback
        f.unop.toOrderHom
    have ht := dgNerveTensorSimplex_pullback R p.1 p.2 f.unop.toOrderHom
    apply (congrArg (fun s => s.map (dgFunctorTensorEvaluation R D E)) ht).trans
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback _ _ _

/-- 概要：元 native dg 関手 end の全単体による実関手族。
方針：同じ同時評価を転置する。規約：core に制限しない。
使われ方：元 end 二単体の全関手圏への像。 -/
def dgFunctorNativeFullFamilyMap : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) := curry (dgFunctorNativeEvaluation R D E)

/-- 概要：元厳密 dg 関手を同じ native end の実頂点として保持する。
方針：元頂点を単位パラメータへ束ねる。規約：同じ関手を保持。
使われ方：全族の元関手への固定。 -/
def dgFunctorNativeFullParameterPoint (F : DGFunctor R D E) :
    𝟙_ SSet.{u + 1} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E) :=
  (unitHomEquiv _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F)

/-- 概要：同じ頂点パラメータの全単体は元単位からの定数族。
方針：元頂点の退化と指定点単体の全作用素則を照合する。
規約：全単体次数の等号。使われ方：同時評価の固定則。 -/
lemma dgFunctorNativeFullParameterPoint_app (F : DGFunctor R D E)
    (n : SimplexCategoryᵒᵖ) (a : (𝟙_ SSet.{u + 1}).obj n) :
    (dgFunctorNativeFullParameterPoint R D E F).app n a =
      dgNativePointSimplex R (DGFunctor R D E) F n.unop.len := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F).pullback
    (SimplexCategory.const n.unop ⦋0⦌ 0).toOrderHom = _
  rw [← dgNativePointSimplex_zero R (DGFunctor R D E) F]
  exact dgNativePointSimplex_pullback R (DGFunctor R D E) F _

/-- 概要：全 native 族を元入力に固定すると元 dg nerve 関手そのもの。
方針：全点単体の tensor 包含と厳密評価固定則を使う。
規約：全単体の厳密等号。使われ方：元全関手族の頂点回収。 -/
lemma dgFunctorNativeEvaluation_fixed (F : DGFunctor R D E) :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⊗ₘ dgFunctorNativeFullParameterPoint R D E F) ≫
      dgFunctorNativeEvaluation R D E =
    (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  ext n p
  rcases p with ⟨x, a⟩
  change (dgNerveTensorSimplex R x
    ((dgFunctorNativeFullParameterPoint R D E F).app n a)).map
      (dgFunctorTensorEvaluation R D E) = x.map F
  rw [dgFunctorNativeFullParameterPoint_app]
  have ht := dgNerveTensorSimplex_point_right R (DGFunctor R D E) x F
  apply (congrArg (fun s => s.map (dgFunctorTensorEvaluation R D E)) ht).trans
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (x.toSimplexData.map _).map _ = x.toSimplexData.map F
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, dgFunctorTensorEvaluation_fixed]

/-- 概要：元 end 全族の同じ指定頂点は元 dg nerve 関手を回収する。
方針：同時評価の厳密固定則を転置する。
規約：頂点同型の任意選択なし。使われ方：元 cone 二単体の指定三関手。 -/
lemma dgFunctorNativeFullFamilyMap_fixed (F : DGFunctor R D E) :
    dgFunctorNativeFullParameterPoint R D E F ≫ dgFunctorNativeFullFamilyMap R D E =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  rw [dgFunctorNativeFullFamilyMap, ← curry_natural_left, curry', ← id_tensorHom,
    dgFunctorNativeEvaluation_fixed]

end SerrePositivity.KST.SConstruction
