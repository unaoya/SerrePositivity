module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeIntervalComponents
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalTriangleIntervalAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoSquareRightPasting

/-!
概要：元の模型三角形比較の普遍作用の像を、既存 native 因子と同じ成分で表す。
方針：全 Hom の二段の指定成分を分解し、同じ元の正方形へ代入する。
規約：native 因子を再選択しない。使われ方：上側因子を元の区間比較へ接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "d₀" => coherentTransformationTotalMap F J (coherentVertexOfHomotopy d)
local notation "c₀" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a) ≫
  coherentTransformationTotalMap G J (coherentVertexOfHomotopy b)
local notation "z" => coherentDiagramTotalVertex J
local notation "U" => coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z
local notation "x" => Sigma.fst (coherentTotalMapNativeRepresentation F J d₀)
local notation "y" => Sigma.fst (coherentTotalMapNativeRepresentation F J c₀)
local notation "A" => pinchedHomLeftToIntervalMappingSpace
  (JoinCocone.vertex (coherentDiagramTotalCocone F)) z ≫
    coherentCoconeIntervalTransportAction F (coherentDiagramTotalCocone F) z

/-- 模型三角形の元の指定比較の像は、同じ既存 native 因子と普遍輸送成分で整合する。 -/
lemma coherentTotalTriangleNativeUniversalSquare :
    coherentTotalTriangleNativeModelComparison T ≪≫
      (coherentTotalMapNativeActionComponentsIso F J c₀).symm ≪≫ FunctorIso.app U y =
    (coherentTotalMapNativeActionComponentsIso F J d₀).symm ≪≫ FunctorIso.app U x ≪≫
      VertexIso.map (coherentTotalTriangleNativeComparison T) A := by
  exact iso_square_paste_right _ _ _ _ _ _ _
    (coherentTotalTriangleNativeComparison_inverse_naturality T)
    (functorIso_app_vertexIso_naturality U (coherentTotalTriangleNativeComparison T))

end SerrePositivity.InfinityCategories.F2
