module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
public import SerrePositivity.AlgebraicGeometry.CechTensorDiagramNaturality
public import SerrePositivity.HomologicalAlgebra.Cech.Filtered
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
概要：指定したfiltered模型の普遍Čech完全性を、同じ終点の普遍完全性へ戻す。
方針：各係数へのtensorは押し出し関手と同型な左随伴で、余極限を保つ。B1のfiltered完全性を使う。
規約：基底の恒等射と元の模型の脚を保ち、終点や係数にNoether仮定を足さない。
使われ方：2iのM12、BM18 Proposition 4.8(1)の構造層でのfilteredな移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

/-- 計画M12：同じ模型の余極限へ、全ての完全係数での完全性を移す。 -/
theorem perfectRingCechUniversalExact_of_filtered_models
    (p : ℕ) {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ Under (CommRingCat.of A)) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ j, PerfectRingCechUniversalExact p (D.obj j).hom.hom) :
    PerfectRingCechUniversalExact p c.pt.hom.hom := by
  intro T _ _ g
  letI := g.toAlgebra
  letI : IsConnected J := IsFiltered.isConnected J
  let F := CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of T)
  letI : F.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso
    (CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of T)).symm
  let U : Under (CommRingCat.of T) ⥤ Arrow CommRingCat.{u} :=
    { obj := fun B ↦ Arrow.mk B.hom
      map := fun f ↦ cechUnderArrowMap f
      map_id := fun B ↦ cechUnderArrowMap_id B
      map_comp := fun f h ↦ cechUnderArrowMap_comp f h }
  let E := D ⋙ F ⋙ U
  let cE := U.mapCocone (F.mapCocone c)
  have hcE : IsColimit cE := by
    apply Comma.fstSndJointlyReflectColimit
    · exact isColimitConstCocone J (CommRingCat.of T)
    · exact isColimitOfPreserves (Under.forget (CommRingCat.of T))
        (isColimitOfPreserves F hc)
  have hE : ∀ j, Cech.IsCechExact (E.obj j) := by
    intro j
    exact hD j T g
  have h := Cech.isCechExact_colimit E hE
  let e := (colimit.isColimit E).coconePointUniqueUpToIso hcE
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso e)).mp h

end SerrePositivity.AlgebraicGeometry.ArcRouteB
