module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionBaseIso

/-!
概要：左右の native 三角形の長辺を、同じ底と始点の prism 延長空間へ揃える。
方針：元の共通長辺の等式と始点固定延長空間の底移送を使う。
規約：同じ全円柱と始点を保持。使われ方：両指定比較の共通空間内での合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "bl" => (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ fst Δ[2] a ≫ dl
local notation "br" => (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ fst Δ[2] a ≫ dr

/-- 左右の長辺に使う共通の底。左の元の長辺をそのまま採用する。 -/
def coherentCospanNativeLongBase : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u} := bl

/-- 右の native 三角形の底の長辺も、同じ指定共通長辺に等しい。 -/
lemma coherentCospanNativeLongBase_right : br = coherentCospanNativeLongBase F X Y Z C b := by
  have hl := congrArg SSet.yonedaEquiv.symm
    (coherentCospanConePointwiseCone_leftTriangle F X Y Z C b)
  have hr := congrArg SSet.yonedaEquiv.symm
    (coherentCospanConePointwiseCone_rightTriangle F X Y Z C b)
  simp only [coherentTransformationPointTriangle, Equiv.symm_apply_apply] at hl hr
  unfold coherentCospanNativeLongBase
  rw [hl, hr]
  have h := congrArg (fun q => fst (Δ[1] : SSet.{u + 1}) a ≫ q)
    (coherentCospanConePointwise_common F X Y Z C b).symm
  simpa only [← Category.assoc, whiskerRight_fst] using h

/-- 元の fiber の始点族が共通の長辺の始点を被覆する。 -/
lemma coherentCospanNativeLongBase_initial :
    s ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ coherentCospanNativeLongBase F X Y Z C b :=
  triangleLongPrism_initial pointedSpaceProjection (fst Δ[2] a ≫ dl) (snd Δ[0] a ≫ s)
    (nativePointedConeTriangle_initial c s hs el)

/-- 両三角形の長辺の指定比較を置く、共通の始点固定 prism 延長空間。 -/
def coherentCospanNativeLongExtensionSpace : SSet.{u + 1} :=
  relativeFunctorExtensionSpace pointedSpaceProjection (coherentCospanNativeLongBase F X Y Z C b)
    (prismEndpoint 0 a) s (coherentCospanNativeLongBase_initial F X Y Z C b)

/-- 共通の長辺延長空間は全高次の選択を含めて可縮な Kan 複体。 -/
lemma coherentCospanNativeLongExtensionSpace_contractible :
    IsContractibleKan (coherentCospanNativeLongExtensionSpace F X Y Z C b) :=
  relativeFunctorExtensionSpace_isContractibleKan pointedSpaceProjection
    (coherentCospanNativeLongBase F X Y Z C b) (prismEndpoint 0 a)
    (prismEndpoint_zero_leftAnodyne a) s (coherentCospanNativeLongBase_initial F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
