module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperUnitFactorValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitTriangleExchange
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoSquareValueTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompCompositionValue

/-!
概要：a6 の既存の上側単位因子を、元の全三角形の指定比較と交換する。
方針：同じ native 単位の交換則を、元の二つの終点等式へ輸送する。
規約：指定単位因子と全三角形を保持。使われ方：値の整合式の上側の外側因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "f₀₁" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "f₁₂" => Subtype.val (leftUnstraighteningMappingVertexMap G J
  (coherentVertexOfHomotopy b))
local notation "f₀₂" => Subtype.val (leftUnstraighteningMappingVertexMap F J
  (coherentVertexOfHomotopy c))

omit [Quasicategory B] in
/-- 最後の辺の単位因子の終点を最初の作用で前合成した、同じ終点表示の等式。 -/
lemma coherentColimitUpperUnitTriangle_target :
    (f₀₁ ≫ f₁₂) ≫ coherentLargeTotalUnit J =
      f₀₁ ≫ ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
        (coherentTransformationTotalMap G J (coherentVertexOfHomotopy b) ≫
          coherentDiagramTotalUnit J)) := by
  exact (Category.assoc _ _ _).trans (congrArg (fun f => f₀₁ ≫ f)
    (coherentTransformationTotalMap_unit_lift G J (coherentVertexOfHomotopy b)))

omit [Quasicategory B] in
/-- 単位作用の後の二作用の合成を、最後の辺の単位因子の前合成の始点へ揃える。 -/
lemma coherentColimitUpperUnitTriangle_middle :
    (f₀₁ ≫ f₁₂) ≫ coherentNativeUnitValueAction J =
      f₀₁ ≫ coherentColimitUpperCompositeAction B b := Category.assoc _ _ _

/-- 既存の長辺・最後の辺の単位因子は、明示した結合則の下で同じ全三角形比較と整合する。 -/
lemma coherentColimitUpperUnitFactor_triangle_exchange :
    functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
        rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)) ≪≫
      (coherentColimitUpperUnitFactorIso B b).precomp f₀₁ =
      coherentColimitUpperUnitFactorIso B c ≪≫
        functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
          (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
          (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)) := by
  have hr := (functorIso_precomp_heq_of_heq
    ((coherentNativeUnitValueIso J).precomp f₁₂) (coherentColimitUpperUnitFactorIso B b)
    rfl (coherentTransformationTotalMap_unit_lift G J (coherentVertexOfHomotopy b))
    (coherentColimitUpperUnitFactorIso_heq_unitValue B b) f₀₁).trans
      (functorIso_precomp_precomp_heq (coherentNativeUnitValueIso J) f₁₂ f₀₁)
  exact functorIso_square_of_heq
    ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
    ((coherentNativeUnitValueIso J).precomp (f₀₁ ≫ f₁₂))
    ((coherentNativeUnitValueIso J).precomp f₀₂)
    ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
    (functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentNativeUnitValueAction J))
      rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b)))
    ((coherentColimitUpperUnitFactorIso B b).precomp f₀₁)
    (coherentColimitUpperUnitFactorIso B c)
    (functorIsoOfEq ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
      (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
      (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)))
    rfl (coherentColimitUpperUnitTriangle_middle (B := B) (a := a) (b := b))
    (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
    (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b))
    (functorIsoOfEq_heq _ rfl _) hr (coherentColimitUpperUnitFactorIso_heq_unitValue B c)
    (functorIsoOfEq_heq
      ((functorTriangleTotalActionIso T).postcomp (coherentLargeTotalUnit J))
      (coherentTransformationTotalMap_unit_lift F J (coherentVertexOfHomotopy c))
      (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)))
    (coherentNativeUnitValueIso_triangle_exchange T)

end SerrePositivity.InfinityCategories.F2
