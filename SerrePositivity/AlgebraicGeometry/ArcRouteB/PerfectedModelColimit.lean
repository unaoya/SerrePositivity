module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelCocone
public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowFamilyColimit
public import SerrePositivity.AlgebraicGeometry.CechTensorDiagramNaturality
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
概要：完全化した同じ有限表示模型の余極限が、元の完全環になることを示す。
方針：既存のFrobeniusと模型の二変数余極限の交換を使い、右端をH01の同型で戻す。
規約：同じSmallModel・指定脚・元の終点を保つ。Noether近似や別の模型の存在を仮定しない。
使われ方：2iのM10、BM18 Proposition 4.8(1)の完全な任意の環への移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画M10：既存の二変数余極限の交換で、同じ元の脚の余極限を得る。 -/
def perfectedModelCoconeIsColimit (p : ℕ) [Fact p.Prime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [PerfectRing A p] [PerfectRing B p] (hp : (p : A) = 0) :
    IsColimit (perfectedModelCocone p A B hp) := by
  let J := FinitePresentationModelIndex A B
  letI : IsConnected J := IsFiltered.isConnected J
  let U : Under (CommRingCat.of A) ⥤ Arrow CommRingCat.{u} :=
    { obj := fun C ↦ Arrow.mk C.hom
      map := fun f ↦ cechUnderArrowMap f
      map_id := fun C ↦ cechUnderArrowMap_id C
      map_comp := fun f g ↦ cechUnderArrowMap_comp f g }
  let D := finitePresentationModelUnderDiagram A B ⋙ U
  let c := U.mapCocone (finitePresentationModelUnderCocone A B)
  have hc : IsColimit c := by
    apply Comma.fstSndJointlyReflectColimit
    · exact isColimitConstCocone J (CommRingCat.of A)
    · exact isColimitOfPreserves (Under.forget (CommRingCat.of A))
        (finitePresentationModelUnderCoconeIsColimit A B)
  let hL (j : J) : (p : (D.obj j).left) = 0 := hp
  let hR (j : J) : (p : (D.obj j).right) = 0 := by
    rw [← map_natCast (D.obj j).hom.hom, hL j, map_zero]
  let hB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), hp, map_zero]
  let cf := frobeniusArrowFamilyTargetCocone D p (Fact.out : p.Prime) hL hR c hp hB
  have hcf : IsColimit cf :=
    frobeniusArrowFamilyTargetCoconeIsColimit D p (Fact.out : p.Prime) hL hR c hp hB hc
  have hr := isColimitOfPreserves (Arrow.rightFunc : Arrow CommRingCat.{u} ⥤ CommRingCat.{u}) hcf
  let e := (perfectFrobeniusLimitEquiv B p (Fact.out : p.Prime) hB
    (perfectRing_primePower_bijective B p (Fact.out : p.Prime) hB)).toCommRingCatIso
  apply isColimitOfReflects (Under.forget (CommRingCat.of A))
  exact IsColimit.ofIsoColimit hr (Cocone.ext e (by intro j; rfl))

end SerrePositivity.AlgebraicGeometry.ArcRouteB
