module
public import SerrePositivity.DifferentialGraded.Perfect.RingHomologyCoverCone
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # 導来対象の有限自由上端被覆と有限射影始域からの射の持ち上げ

既存の任意のHasDerivedCategoryを使う。導来圏のモデルや射クラスは変更しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringComplexDerived_map_surjective (P : Complex A) (hP : strictlyPerfectComplex A P)
    (K : Complex A) : Function.Surjective (DerivedCategory.Q.map (X := P) (Y := K)) := by
  let := strictlyPerfectComplex_isKProjective A P hP
  let q := _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  intro f
  obtain ⟨u, hu⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (q.obj K)).2
    (e.hom.app P ≫ f ≫ e.inv.app K)
  obtain ⟨g, hg⟩ := q.map_surjective u
  refine ⟨g, (cancel_epi (e.hom.app P)).1 ?_⟩
  have h := e.hom.naturality g
  change DerivedCategory.Qh.map (q.map g) ≫ e.hom.app K = e.hom.app P ≫
    DerivedCategory.Q.map g at h
  rw [hg, hu] at h
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h.symm

lemma ringDerived_homologyMap_epi_of_chainMap {P K : Complex A} (f : P ⟶ K) (n : ℤ)
    [Epi (homologyMap f n)] :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (DerivedCategory.Q.map f)) := by
  let e := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
  have h : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (DerivedCategory.Q.map f) = e.hom.app P ≫ homologyMap f n ≫ e.inv.app K := by
    apply (cancel_mono (e.hom.app K)).1
    have hn : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (DerivedCategory.Q.map f) ≫ e.hom.app K = e.hom.app P ≫ homologyMap f n :=
      e.hom.naturality f
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, ← Category.assoc]
    exact hn.trans (Category.comp_id _).symm
  rw [h]
  infer_instance

lemma ringDerived_exists_finiteFree_homologyCover (X : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X)] :
    ∃ (m : ℕ) (f : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj
        (ModuleCat.of A (Fin m → A))) ⟶ X),
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let eh : H.obj X ≅ K.homology n := (H.mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K
  let : Module.Finite A (K.homology n) := Module.Finite.equiv eh.toLinearEquiv
  obtain ⟨m, f, hf⟩ := ringComplex_exists_finiteFree_homologyCover A K n
  let := hf
  let := ringDerived_homologyMap_epi_of_chainMap A f n
  refine ⟨m, DerivedCategory.Q.map f ≫ e.hom, ?_⟩
  rw [H.map_comp]
  infer_instance

lemma ringDerivedRetract_topHomology_finite_usual (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0)
    {X : DerivedCategory (ModuleCat.{u} A)} (a : Retract X (DerivedCategory.Q.obj P)) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X) := by
  let : Module.Finite A
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).obj P) :=
    ringComplex_topHomology_finite A P n hd
  exact finiteModule_of_retract A
    ((a.map (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n)).trans
      (Retract.ofIso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app P)))

end SerrePositivity.DifferentialGraded
