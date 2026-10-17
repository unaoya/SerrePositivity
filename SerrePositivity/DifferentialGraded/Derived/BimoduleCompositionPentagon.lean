module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonFamilies

/-! # 全導来bimodule因子上の五角恒等式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

omit [DGCategory A B] [DGCategory A F] [DGCategory A G]
    [Small.{u} B] [Small.{u} F] [Small.{u} G] in
lemma exists_rightKFlat_derived_iso (hE : localHomKFlat A E)
    (M : DerivedBimoduleCategory A C E) :
    ∃ P : RightKFlatBimoduleCategory A C E,
      Nonempty ((bimoduleToDerived A C E).obj P.obj ≅ M) := by
  let J := rightKFlatDerivedInclusion A C E
  let L := rightKFlatToDerived A C E
  let : J.EssSurj := rightKFlatDerivedInclusion_essSurj A C E hE
  let X := J.objPreimage M
  let P := L.objPreimage X
  refine ⟨P, ⟨?_⟩⟩
  exact J.mapIso (L.objObjPreimageIso X) ≪≫ J.objObjPreimageIso M

/-- 全三つの導来後因子について五角の二経路が一致する。前因子にも自然。 -/
lemma derivedBimodulePentagon (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E F)
    (S : DerivedBimoduleCategory A F G) :
    derivedBimodulePentagonShort A B C E F G hE hF hG Q R S =
      derivedBimodulePentagonLong A B C E F G hE hF hG Q R S := by
  let T := DerivedBimoduleCategory A C E ×
    (DerivedBimoduleCategory A E F × DerivedBimoduleCategory A F G)
  let q : T ⥤ DerivedBimoduleCategory A C E := CategoryTheory.Prod.fst _ _
  let r : T ⥤ DerivedBimoduleCategory A E F :=
    CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.fst _ _
  let s : T ⥤ DerivedBimoduleCategory A F G :=
    CategoryTheory.Prod.snd _ _ ⋙ CategoryTheory.Prod.snd _ _
  let U := compositionFamily
    (compositionFamily (q ⋙ derivedBimoduleComposeFunctor A B C E hE)
      (r ⋙ derivedBimoduleComposeFunctor A B E F hF))
    (s ⋙ derivedBimoduleComposeFunctor A B F G hG)
  let a := derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s
  let b := derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s
  obtain ⟨Q₀, ⟨eQ⟩⟩ := exists_rightKFlat_derived_iso A C E hE Q
  obtain ⟨R₀, ⟨eR⟩⟩ := exists_rightKFlat_derived_iso A E F hF R
  obtain ⟨S₀, ⟨eS⟩⟩ := exists_rightKFlat_derived_iso A F G hG S
  let V : T := ((bimoduleToDerived A C E).obj Q₀.obj,
    ((bimoduleToDerived A E F).obj R₀.obj, (bimoduleToDerived A F G).obj S₀.obj))
  let e : V ≅ (Q, (R, S)) := eQ.prod (eR.prod eS)
  have hV : a.app V = b.app V := by
    change (derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s).app V =
      (derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s).app V
    rw [derivedBimodulePentagonShortFamily_app, derivedBimodulePentagonLongFamily_app]
    exact derivedBimodulePentagon_kFlat A B C E F G hE hF hG Q₀ R₀ S₀
  have h : a.app (Q, (R, S)) = b.app (Q, (R, S)) := by
    apply (Iso.cancel_iso_hom_left (U.mapIso e) _ _).1
    change U.map e.hom ≫ _ = U.map e.hom ≫ _
    rw [a.naturality, b.naturality, hV]
  change (derivedBimodulePentagonShortFamily A B C E F G hE hF hG q r s).app (Q, (R, S)) =
    (derivedBimodulePentagonLongFamily A B C E F G hE hF hG q r s).app (Q, (R, S)) at h
  rw [derivedBimodulePentagonShortFamily_app, derivedBimodulePentagonLongFamily_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
