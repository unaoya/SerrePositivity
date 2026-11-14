module
public import SerrePositivity.KST.SConstruction.DGOdotTargetRightEnd
public import SerrePositivity.KST.SConstruction.DGPerfectEndRepresentation

/-! # 同じ指定商 End の実 cone 作用と右像の代表加群作用
概要：元の商からの cone 関手を指定 End へ制限し、同じ右像への Yoneda 作用と比較する。
方針：元の商延長の全 Hom 評価を、同じ右 cone 閉同型の全次数可換式へ前合成する。
規約：同じ実 cone 関手と元の閉同型を保持。使われ方：実 ⊙ 比較の代表加群上の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (G)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (DRaw) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (DRaw) (E) (L) (G) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "e" => dgOdotTargetRightConeIso R d

/-- 元の商延長を指定 End に制限した、同じ実 cone 加群上の作用。 -/
def dgOdotQuotientConeRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (DGOdotCorner R d)) :=
  (((I).endInclusion).comp (dgOdotTargetQuotientFunctor R d)).comp
    (perfectDGModuleInclusion R (DGOdotCorner R d) Set.univ)

/-- 同じ指定商 End 比較の先で、元の右像の代表加群に作用する実関手。 -/
def dgOdotQuotientRightRepresentation :
    DGFunctor R (DGOdotQuotientEnd R d) (RightModule R (DGOdotCorner R d)) :=
  ((dgOdotTargetRightEndMap R d).comp (endomorphismInclusion R ((qS).obj (I).rightPoint))).comp
    (dgYoneda R (DGOdotCorner R d))

/-- 元の cone 表現は、同じ指定商 End 延長の全 Hom 作用を回収する。 -/
lemma dgOdotQuotientConeRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotQuotientConeRepresentation R d).map x y =
      (dgOdotTargetQuotientEndMap R d).map x y := by
  change (𝟙 _ ≫ (dgOdotTargetQuotientEndMap R d).map x y) ≫ 𝟙 _ = _
  erw [Category.id_comp, Category.comp_id]

/-- 元の Yoneda で戻した比較は、同じ右 cone 閉同型による実 End 共役。 -/
lemma dgOdotTargetRightEndHom_yoneda :
    dgOdotTargetRightEndHom R d ≫ yonedaHom R (DGOdotCorner R d) ((qS).obj (I).rightPoint)
      ((qS).obj (I).rightPoint) =
      dgPerfectEndIsoModuleHom R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point) ((qS).obj
        (I).rightPoint) (e) :=
  dgPerfectEndIsoObjectHom_yoneda R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point) ((qS).obj
    (I).rightPoint) (e)

/-- 右像の実代表加群上の作用は、同じ商 End 作用に同じ閉共役を合成したもの。 -/
lemma dgOdotQuotientRightRepresentation_map (x y : DGOdotQuotientEnd R d) :
    (dgOdotQuotientRightRepresentation R d).map x y =
      (dgOdotTargetQuotientEndMap R d).map x y ≫
        dgPerfectEndIsoModuleHom R (DGOdotCorner R d) (dgOdotTargetCone R d (I).point) ((qS).obj
          (I).rightPoint) (e) := by
  change ((dgOdotTargetRightEndMap R d).map x y ≫ 𝟙 _) ≫
    yonedaHom R (DGOdotCorner R d) ((qS).obj (I).rightPoint) ((qS).obj (I).rightPoint) = _
  rw [Category.comp_id, dgOdotTargetRightEndMap_map]
  erw [Category.assoc, dgOdotTargetRightEndHom_yoneda]
  rfl

/-- 元の右 cone 閉同型は、二つの実商 End 表現を全 Hom 複体について結ぶ。 -/
lemma dgOdotQuotientRepresentation_naturality (x y : DGOdotQuotientEnd R d) :
    (dgOdotQuotientConeRepresentation R d).map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (dgOdotTargetCone R d
        (I).point).val) (e).hom =
    (dgOdotQuotientRightRepresentation R d).map x y ≫
      eHomWhiskerRight (Complex R) (e).hom
        (ForgetEnrichment.of (Complex R) (representable R ((qS).obj (I).rightPoint))) := by
  rw [dgOdotQuotientConeRepresentation_map, dgOdotQuotientRightRepresentation_map]
  exact dgPerfectEndRepresentation_precompose R (DGOdotCorner R d) (dgOdotTargetCone R d
    (I).point) ((qS).obj (I).rightPoint) (e) _

/-- 同じ商 cone 作用と元の右像作用を結ぶ全次数自然比較。成分は元の閉同型。 -/
def dgOdotQuotientRepresentationComparison :=
  dgFunctorClosedComparison R (dgOdotQuotientConeRepresentation R d)
    (dgOdotQuotientRightRepresentation R d) (fun _ => (e).hom)
    (dgOdotQuotientRepresentation_naturality R d)

/-- 同じ元の閉同型の逆を使う、全次数自然な逆比較。 -/
def dgOdotQuotientRepresentationInverseComparison :=
  dgFunctorClosedInverseComparison R (dgOdotQuotientConeRepresentation R d)
    (dgOdotQuotientRightRepresentation R d) (fun _ => (e))
    (dgOdotQuotientRepresentation_naturality R d)

/-- 元の閉零射圏でも同じ商 End 表現を元の成分のまま比較する自然同型。 -/
def dgOdotQuotientRepresentationClosedIso :
    (dgOdotQuotientConeRepresentation R d).onClosed ≅
      (dgOdotQuotientRightRepresentation R d).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (fun _ => (e))
    (dgOdotQuotientRepresentation_naturality R d)

end SerrePositivity.KST.SConstruction
