module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSimplicialHomTransportRestriction
public import SerrePositivity.InfinityCategories.F1.PathCorrectedFunctorSquare
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostLifting
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence

/-!
概要：任意の単射な境界への指定自然性を保持して、元の Hom 輸送を厳密に可換にする。
方針：同じ分類先の制限に沿って指定 path を持ち上げ、固定境界 fiber へ制限する。
規約：元の Hom 輸送への指定同型を保持し、境界の nerve 表示を要求しない。
使われ方：セル延長空間の target 側の境界固定の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C] {A : SSet.{u + 1}}
  (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) [Mono a] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "R₀" => cocartesianBaseChangeSimplicialRestrictionZero a k p q
local notation "R₁" => cocartesianBaseChangeSimplicialRestrictionOne a k p q
local notation "U" => cocartesianBaseChangeHomTransport k p q
local notation "V" => cocartesianBaseChangeSimplicialHomTransport a k p q

/-- 同じ指定 path を保ち、境界への制限と厳密に可換にした元の Hom 輸送。 -/
def cocartesianBaseChangeSimplicialHomCorrection :
    PathCorrectedFunctorSquare R₀ U (R₁ ≫ V)
      (cocartesianBaseChangeHomTransport_simplicialRestrictionIso a k p q).symm :=
  pathCorrectedFunctorSquare R₀
    (kanEquivalenceLifting_intervalMappingPostOfEq ((pre a).app CatInfinity)
      (F1B.kanEquivalenceLifting_pre a) _ _ rfl rfl) U (R₁ ≫ V)
    (cocartesianBaseChangeHomTransport_simplicialRestrictionIso a k p q).symm

/-- 補正した同じ全 Hom の輸送。 -/
def cocartesianBaseChangeSimplicialCorrectedHomTransport :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).map

/-- 指定された元の境界輸送への制限は厳密に一致する。 -/
lemma cocartesianBaseChangeSimplicialCorrectedHomTransport_comm :
    cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q ≫ R₀ = R₁ ≫ V :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).comm

/-- 補正した輸送は、同じ指定 path で元の輸送と同型。 -/
def cocartesianBaseChangeSimplicialCorrectedHomTransportIso :
    FunctorIso (cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) U :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).exactComponentIso

/-- 同じ補正輸送は、追加仮定なしに全 Hom の同値。 -/
lemma cocartesianBaseChangeSimplicialCorrectedHomTransport_isQCatEquivalence :
    IsQCatEquivalence (cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) :=
  (cocartesianBaseChangeSimplicialHomCorrection a k p q).map_isQCatEquivalence
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

variable (r : (intervalMappingSpace
  (functorVertex (a ≫ cocartesianStrictTransportCoherentDiagram
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom))
  (functorVertex (a ≫ cocartesianStrictTransportCoherentDiagram
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom))) _⦋0⦌)

/-- 指定された境界値を固定した、同じ補正輸送の実際の fiber 上の射。 -/
def cocartesianBaseChangeSimplicialBoundaryFiberTransport :
    vertexFiber R₁ r ⟶ vertexFiber R₀ ((V).app (Opposite.op ⦋0⦌) r) :=
  vertexFiberLift R₀ ((V).app (Opposite.op ⦋0⦌) r)
    (vertexFiberι R₁ r ≫ cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q) (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun m ↦ vertexFiberι R₁ r ≫ m)
          (cocartesianBaseChangeSimplicialCorrectedHomTransport_comm a k p q)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun m ↦ m ≫ V) (vertexFiberι_comp R₁ r)).trans
              (SSet.const_comp _ _)))))

/-- 同じ境界固定の射は、元の全 Hom への射影を保持する。 -/
lemma cocartesianBaseChangeSimplicialBoundaryFiberTransport_ι :
    cocartesianBaseChangeSimplicialBoundaryFiberTransport a k p q r ≫
      vertexFiberι R₀ ((V).app (Opposite.op ⦋0⦌) r) =
    vertexFiberι R₁ r ≫ cocartesianBaseChangeSimplicialCorrectedHomTransport a k p q :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories
