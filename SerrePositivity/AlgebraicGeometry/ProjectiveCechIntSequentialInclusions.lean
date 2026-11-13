module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFilteredInclusions
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequential

/-!
概要：整数係数 Čech H の順極限比較と各自然数段の標準写像の整合性。
方針：AsSmall ℕ への添字の移送について final な関手の標準写像の公式を使う。
規約：既存の projectiveIntCechSequentialHomologyIso を照合する。
使われ方：Frobenius 系の各段からの H⁰ の増大写像の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 整数係数の Čech H の順極限比較は各自然数段からの標準写像を保つ。 -/
theorem projectiveIntCechSequentialHomologyIso_ι
    (D : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ) (n q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
        (fullCechComplexMap (colimit.ι D n)) ≫
      (projectiveIntCechSequentialHomologyIso D q).hom =
    colimit.ι (D ⋙ fullCechComplexFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) n := by
  let H := fullCechComplexFunctor (R := ℤ) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let e : AsSmall.{u} ℕ ⥤ ℕ := AsSmall.equiv.symm.functor
  let k : AsSmall.{u} ℕ := AsSmall.up.obj n
  simp only [projectiveIntCechSequentialHomologyIso,
    projectiveIntCechSequentialHomologyNatIso, Iso.app_hom,
    Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Final.colimIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  change H.map (colimit.ι D (e.obj k)) ≫ _ = _
  rw [← H.map_comp_assoc, Final.ι_colimitIso_inv]
  have h := projectiveIntCechFilteredHomologyIso_ι (e ⋙ D) k q
  simp only [projectiveIntCechFilteredHomologyIso, Iso.app_hom] at h
  change H.map (colimit.ι (e ⋙ D) k) ≫ _ = _ at h
  rw [← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ (Final.colimitIso e (D ⋙ H)).hom) h).trans
    (Final.ι_colimitIso_hom e (D ⋙ H) k)

end SerrePositivity.AlgebraicGeometry
