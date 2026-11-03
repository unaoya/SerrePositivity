module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # 全 Hom の可換式からの閉零 dg 自然比較
概要：全 Hom 複体上で自然な閉零射族を、単位パラメータの豊穣自然変換へ束ねる。
方針：単位因子の braiding と左右 unitor を消し、前後合成の等式を使う。
規約：通常の閉零射圏の自然性だけを入力にしない。使われ方：Perf 延長の恒等・合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] (F G : DGFunctor A D E)

/-- 全次数 Hom に関して自然な閉零射族の、元の dg 豊穣自然変換。 -/
def dgFunctorClosedComparison
    (a : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (a y) =
      G.map x y ≫
        eHomWhiskerRight (Complex A) (a x) (ForgetEnrichment.of (Complex A) (G.obj y))) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A))) F G where
  app x := ForgetEnrichment.homTo (Complex A) (a x)
  naturality x y := by
    change (β_ (𝟙_ (Complex A)) (x ⟶[Complex A] y)).hom ≫
        (F.map x y ⊗ₘ ForgetEnrichment.homTo (Complex A) (a y)) ≫
          eComp (Complex A) _ _ _ =
      (ForgetEnrichment.homTo (Complex A) (a x) ⊗ₘ G.map x y) ≫
        eComp (Complex A) _ _ _
    apply (cancel_epi (λ_ (x ⟶[Complex A] y)).inv).1
    rw [braiding_tensorUnit_left]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [rightUnitor_inv_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
    exact h x y

/-- 豊穣自然比較の成分は、入力した元の閉零射を保持する。 -/
lemma dgFunctorClosedComparison_app
    (a : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (Complex A) (G.obj x)) (h) (x : D) :
    (dgFunctorClosedComparison A F G a h).app x =
      ForgetEnrichment.homTo (Complex A) (a x) := rfl

/-- 全 Hom に関して自然な閉零同型族の逆も、全 Hom に関して自然。 -/
lemma dgFunctorClosedComparison_inv_naturality
    (e : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ≅
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom =
      G.map x y ≫
        eHomWhiskerRight (Complex A) (e x).hom (ForgetEnrichment.of (Complex A) (G.obj y)))
    (x y : D) :
    G.map x y ≫ eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (G.obj x)) (e y).inv =
      F.map x y ≫
        eHomWhiskerRight (Complex A) (e x).inv (ForgetEnrichment.of (Complex A) (F.obj y)) := by
  have hh := congrArg (fun k => k ≫
    eHomWhiskerRight (Complex A) (e x).inv (ForgetEnrichment.of (Complex A) (G.obj y)) ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (G.obj x)) (e y).inv)
    (h x y)
  have hx := eHom_whisker_exchange (Complex A) (C := ClosedCategory A E)
    (e x).inv (e y).hom
  rw [Category.assoc, Category.assoc, ← Category.assoc
    (eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom), hx] at hh
  simpa only [Category.assoc,
    ← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, eHomWhiskerLeft_id, eHomWhiskerRight_id,
    Category.comp_id, Category.id_comp] using hh.symm

/-- 全次数自然な閉零同型族の逆向きの豊穣自然変換。 -/
def dgFunctorClosedInverseComparison
    (e : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ≅
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom =
      G.map x y ≫
        eHomWhiskerRight (Complex A) (e x).hom (ForgetEnrichment.of (Complex A) (G.obj y))) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A))) G F :=
  dgFunctorClosedComparison A G F (fun x => (e x).inv)
    (dgFunctorClosedComparison_inv_naturality A F G e h)

end SerrePositivity.KST.SConstruction
