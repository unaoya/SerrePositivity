module

public import SerrePositivity.EInfinity.Modules.CotensorScalar
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainComonoid
public import Mathlib.CategoryTheory.Whiskering

/-!
# 同じ正規化標準単体を係数とする加群 cotensor の全族

概要：M10 の具体的な right frame 候補を、面・退化・全加群射に関手的に構成する。
方針：既存の正規化標準単体関手と同じ反変 cotensor 関手を合成する。
規約：HA §1.3.4、Reedy fibrancy と局所化への同値は別に証明する。
使われ方：モデル frame Hom と元の dg Hom の同じ全単体の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ標準単体の cotensor 関手を全単体作用素で束ねる。
方針：既存の正規化関手と係数反変関手を合成する。
規約：HA §1.3.4、全ての面と退化。使われ方：元の simplicial 加群族。 -/
def moduleCotensorSimplexFamily :
    SimplexCategoryᵒᵖ ⥤ (ModuleCategory A D ⥤ ModuleCategory A D) :=
  (SSet.stdSimplex ⋙ SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).op ⋙
    moduleCotensorScalarFunctor A D

/-- 概要：同じ simplicial cotensor は全ての元の加群射に関手的。
方針：元の二変数関手の順を入れ替える。
規約：HA §1.3.4、同じ全単体の関手族。使われ方：全標的の frame Hom。 -/
def moduleCotensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategoryᵒᵖ ⥤ ModuleCategory A D) :=
  (moduleCotensorSimplexFamily A D).flip

/-- 概要：元の一つの加群の同じ simplicial cotensor。
方針：全加群族を評価する。
規約：HA §1.3.4、元の加群を保持。使われ方：具体的な frame 候補。 -/
abbrev moduleCotensorSimplices (M : ModuleCategory A D) :
    SimplexCategoryᵒᵖ ⥤ ModuleCategory A D :=
  (moduleCotensorSimplicesFunctor A D).obj M

/-- 概要：同じ simplicial cotensor の台は元の正規化単体からの内部 Hom。
方針：関手の合成を評価する。
規約：HA §1.3.4、全次元。使われ方：同じ実 dg Hom との単体比較。 -/
lemma moduleCotensorSimplices_obj_eval (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).obj ((moduleCotensorSimplices A D M).obj n) =
      homComplex A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).obj M) := rfl

/-- 概要：同じ面・退化の作用は元の正規化鎖写像による前合成。
方針：同じ係数前合成の評価式を使う。
規約：HA §1.3.4、全単体作用素。使われ方：台での Reedy 境界の照合。 -/
lemma moduleCotensorSimplices_map_eval (M : ModuleCategory A D)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : D) :
    (moduleEvaluation A D x).map ((moduleCotensorSimplices A D M).map f) =
      homPrecompose
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (SSet.stdSimplex.map f.unop))
        ((moduleEvaluation A D x).obj M) :=
  moduleCotensorPreMap_eval A D _ M x

/-- 概要：同じ全加群射の作用は元の Hom 後合成。
方針：同じ反変係数関手族を評価する。
規約：HA §1.3.4、全次元・全加群射。使われ方：全標的の自然性。 -/
lemma moduleCotensorSimplicesFunctor_map_eval {M N : ModuleCategory A D} (g : M ⟶ N)
    (n : SimplexCategoryᵒᵖ) (x : D) :
    (moduleEvaluation A D x).map (((moduleCotensorSimplicesFunctor A D).map g).app n) =
      homPostcompose
        (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n.unop))
        ((moduleEvaluation A D x).map g) :=
  moduleCotensorMap_eval A D _ g x

/-- 概要：元の加群から同じ simplicial cotensor への全単体 Hom。
方針：元の通常 Hom 関手を後合成する。
規約：HA §1.3.4、Kan 性は別に示す。使われ方：同じモデル frame Hom の候補。 -/
def moduleCotensorMappingSimplices (P M : ModuleCategory A D) : SSet.{u} :=
  moduleCotensorSimplices A D M ⋙ coyoneda.obj (op P)

/-- 概要：同じ全単体 Hom は全ての元の標的加群に関手的。
方針：同じ simplicial 族の後で Hom を各次数に作用させる。
規約：HA §1.3.4、同じ Hom 射。使われ方：全標的の写像空間比較。 -/
def moduleCotensorMappingFunctor (P : ModuleCategory A D) :
    ModuleCategory A D ⥤ SSet.{u} :=
  moduleCotensorSimplicesFunctor A D ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCategory A D) (Type u)).obj
      (coyoneda.obj (op P))

end SerrePositivity.EInfinity.Modules
