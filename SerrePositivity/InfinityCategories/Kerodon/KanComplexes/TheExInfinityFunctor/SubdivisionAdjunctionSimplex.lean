module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexSimplex

/-!
# 細分随伴の各単体での評価

概要：sd⊣Ex の Hom 同値を標準単体の細分からの射で計算する。
方針：Mathlib の制限 Yoneda 随伴の成分の式を、標準細分の同型で書く。
規約：二重細分の境界条件の射の等式に用いる補助。
使われ方：horn の細分比較の包含との整合。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite

/--
概要：細分随伴の Hom 同値を、各単体で明示的な射の合成として評価する。
方針：制限 Yoneda 随伴の一般公式を標準同型で型付けして適用する。
規約：Ex の単体の ULift の down を取った式。
使われ方：二重細分の horn 上での境界の一致。
-/
theorem subdivisionHomEquiv_app_down (X Y : SSet.{u}) (f : SSet.sd.obj X ⟶ Y)
    (n : SimplexCategory) (s : X.obj (op n)) :
    (((SSet.sdExAdjunction.homEquiv X Y) f).app (op n) s).down =
      SSet.stdSimplex.sdIso.inv.app n ≫ SSet.sd.map (SSet.yonedaEquiv.symm s) ≫ f := by
  have h : ((SSet.sdExAdjunction.homEquiv X Y) f).app (op n) s =
      ULift.up (SSet.stdSimplex.sdIso.inv.app n ≫ SSet.sd.map (SSet.yonedaEquiv.symm s) ≫ f) :=
    Presheaf.uliftYonedaAdjunction_homEquiv_app.{0} SSet.sd.{u} SSet.stdSimplex.sdIso.{u}.inv f s
  exact congrArg ULift.down h

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
