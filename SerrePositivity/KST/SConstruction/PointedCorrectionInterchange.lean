module
public import SerrePositivity.KST.SConstruction.FamilyChainInterchangeGluing
public import SerrePositivity.KST.SConstruction.EdgeFamilyCylinders
public import SerrePositivity.KST.SConstruction.PointParameterMaps
public import SerrePositivity.KST.Spectra.PointedEnrichment

/-! # 元の raw 補正と BF 比較を同じ二時刻で合成する
概要：後続 raw 補正と先行 BF 比較を独立な時刻で合成し、元の全四辺を回収する。
方針：積の交換から正しい順序の豊穣合成を作り、元の全交換正方形を使う。
規約：充填や辺の選び直しを行わず、元の同じ全二円柱を保持する。
使われ方：三入力の左右補正辺路に現れる、前二射の比較と最終射の補正の交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance correctionInterchangePointedSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 後続 raw 射、先行 BF 射の順の入力を、同じ正しい順序で豊穣合成する実写像。 -/
def pointedReverseComposition (A B C : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom B C).right ⊗ (PointedObject.basedHom A B).right ⟶
      (PointedObject.basedHom A C).right :=
  (β_ (PointedObject.basedHom B C).right (PointedObject.basedHom A B).right).hom ≫
    eComp SSet A B C

/-- 元の同じ二族は、入力順を合わせた同じ豊穣合成へ写る。 -/
lemma pointedReverseComposition_lift {U : SSet.{u}} {A B C : PointedSimplicialSet.{u}}
    (h : U ⟶ (PointedObject.basedHom B C).right)
    (k : U ⟶ (PointedObject.basedHom A B).right) :
    lift h k ≫ pointedReverseComposition A B C = lift k h ≫ eComp SSet A B C := by
  rw [pointedReverseComposition, ← Category.assoc, lift_braiding_hom]

variable {U : SSet.{u}} {A B C : PointedSimplicialSet.{u}}
  (h : U ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom B C).right)
  (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom A B).right)

/-- 元の補正と比較の両全円柱を、独立な二時刻で合成した同じ実正方形。 -/
def pointedCorrectionInterchange := familyInterchangeSquare h k (pointedReverseComposition A B C)

/-- 補正時刻の零面は、元の全 BF 比較と元の補正始点の同じ合成。 -/
lemma pointedCorrectionInterchange_first_zero :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ pointedCorrectionInterchange h k =
      lift k (fst U Δ[1] ≫ SSet.ι₀ ≫ h) ≫ eComp SSet A B C := by
  rw [pointedCorrectionInterchange, familyInterchangeSquare_first_zero,
    pointedReverseComposition_lift]

/-- 補正時刻の一面は、元の全 BF 比較と元の補正終点の同じ合成。 -/
lemma pointedCorrectionInterchange_first_one :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ pointedCorrectionInterchange h k =
      lift k (fst U Δ[1] ≫ SSet.ι₁ ≫ h) ≫ eComp SSet A B C := by
  rw [pointedCorrectionInterchange, familyInterchangeSquare_first_one,
    pointedReverseComposition_lift]

/-- BF 比較時刻の零面は、元の比較始点と元の全補正円柱の同じ合成。 -/
lemma pointedCorrectionInterchange_second_zero :
    SSet.ι₀ ≫ pointedCorrectionInterchange h k =
      lift (fst U Δ[1] ≫ SSet.ι₀ ≫ k) h ≫ eComp SSet A B C := by
  rw [pointedCorrectionInterchange, familyInterchangeSquare_second_zero,
    pointedReverseComposition_lift]

/-- BF 比較時刻の一面は、元の比較終点と元の全補正円柱の同じ合成。 -/
lemma pointedCorrectionInterchange_second_one :
    SSet.ι₁ ≫ pointedCorrectionInterchange h k =
      lift (fst U Δ[1] ≫ SSet.ι₁ ≫ k) h ≫ eComp SSet A B C := by
  rw [pointedCorrectionInterchange, familyInterchangeSquare_second_one,
    pointedReverseComposition_lift]

/-- 元の全共通パラメータの制限は、同じ二時刻正方形の構成と厳密に可換。 -/
lemma pointedCorrectionInterchange_restrict {T : SSet.{u}} (j : T ⟶ U) :
    ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ pointedCorrectionInterchange h k =
      pointedCorrectionInterchange ((j ▷ (Δ[1] : SSet.{u})) ≫ h)
        ((j ▷ (Δ[1] : SSet.{u})) ≫ k) :=
  familyInterchangeSquare_restrict _ _ _ _

/-- BF 側が元の実辺の円柱なら、指定点での全正方形は同じ元の二辺の積の像。 -/
lemma pointedCorrectionInterchange_point {a b : (PointedObject.basedHom A B).right _⦋0⦌}
    (v : U _⦋0⦌) (e : ((PointedObject.basedHom A B).right).Edge a b) :
    (pointParameterMap v (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫
        pointedCorrectionInterchange h (edgeFamilyCylinder (U := U) e) =
      lift (fst (Δ[1] : SSet.{u}) Δ[1] ≫ pointParameterMap v Δ[1] ≫ h)
        (snd (Δ[1] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) ≫
          pointedReverseComposition A B C := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.KST.SConstruction
