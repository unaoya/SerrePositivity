module
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionInputLaws

/-!
概要：同じ cone 関手から作る既存の懸垂射データの厳密恒等則・合成則。
方針：指定 cell 比較の厳密則を元の ofConeFunctor と同じ実商へ代入する。
規約：cone 射や全 native Hom の存在は主張しない。分解データを新たに選び直さない。
使われ方：D-8 e の同じ cone 上の作用を、元の K-B 懸垂射へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded KST.NonConnective
variable (R : Type u) [CommRing R] (D E B : Type v)
  [DGCategory R D] [DGCategory R E] [DGCategory R B]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (J : DGKappaConeInput R E κ)
  (K : DGKappaConeInput R B κ)

theorem dgKappaSuspensionMapDataOfCone_identity :
    DGKappaSuspensionMapData.ofConeFunctor R D D I I (DGFunctor.id _)
      (fun _ hx => hx) = DGKappaSuspensionMapData.id R D I := by
  apply DGKappaSuspensionMapData.ext
  · rfl
  · exact DGCategoryCellResolution.comparisonFunctor_identity R (DGKappaCone R D I)

theorem dgKappaSuspensionMapDataOfCone_composition
    (F : DGFunctor R (DGKappaCone R D I) (DGKappaCone R E J))
    (G : DGFunctor R (DGKappaCone R E J) (DGKappaCone R B K))
    (hF : ∀ x ∈ dgKappaConePerfectObjects R D I,
      F.obj x ∈ dgKappaConePerfectObjects R E J)
    (hG : ∀ x ∈ dgKappaConePerfectObjects R E J,
      G.obj x ∈ dgKappaConePerfectObjects R B K) :
    DGKappaSuspensionMapData.ofConeFunctor R D B I K (F.comp G)
      (fun x hx => hG _ (hF x hx)) =
      DGKappaSuspensionMapData.comp R D E I J
        (DGKappaSuspensionMapData.ofConeFunctor R D E I J F hF)
        (DGKappaSuspensionMapData.ofConeFunctor R E B J K G hG) := by
  apply DGKappaSuspensionMapData.ext
  · rfl
  · exact DGCategoryCellResolution.comparisonFunctor_composition R
      (DGKappaCone R D I) (DGKappaCone R E J) (DGKappaCone R B K) F G

theorem dgKappaSuspensionInputMapOfCone_identity :
    dgKappaSuspensionInputMap R D D I I
      (DGKappaSuspensionMapData.ofConeFunctor R D D I I (DGFunctor.id _) (fun _ hx => hx)) =
      𝟙 (dgKappaSuspensionKInput R D I) := by
  rw [dgKappaSuspensionMapDataOfCone_identity, dgKappaSuspensionInputMap_id]

theorem dgKappaSuspensionInputMapOfCone_composition
    (F : DGFunctor R (DGKappaCone R D I) (DGKappaCone R E J))
    (G : DGFunctor R (DGKappaCone R E J) (DGKappaCone R B K))
    (hF : ∀ x ∈ dgKappaConePerfectObjects R D I,
      F.obj x ∈ dgKappaConePerfectObjects R E J)
    (hG : ∀ x ∈ dgKappaConePerfectObjects R E J,
      G.obj x ∈ dgKappaConePerfectObjects R B K) :
    dgKappaSuspensionInputMap R D B I K
      (DGKappaSuspensionMapData.ofConeFunctor R D B I K (F.comp G) (fun x hx => hG _ (hF x hx))) =
      dgKappaSuspensionInputMap R D E I J
        (DGKappaSuspensionMapData.ofConeFunctor R D E I J F hF) ≫
      dgKappaSuspensionInputMap R E B J K
        (DGKappaSuspensionMapData.ofConeFunctor R E B J K G hG) := by
  rw [dgKappaSuspensionMapDataOfCone_composition, dgKappaSuspensionInputMap_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
