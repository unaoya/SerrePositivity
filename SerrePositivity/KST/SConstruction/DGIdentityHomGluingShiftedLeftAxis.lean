module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeAxes
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingComparison

/-!
概要：元厳密比較の始域上で元 shifted 左軸を全関手として回収する。
方針：元 cone 左軸の全 Hom 回収を同じ実 dg shift で後合成する。
規約：元対象・全鎖写像・指定 shift を保持する。
使われ方：元実逆回転の二実像比較を元始域へ制限する右軸照合。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma postIdentityShift {V : Type*} [Category V] {X Y Z W T : V}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (d : W ⟶ T) (p : X ⟶ W)
    (h : a ≫ (b ≫ 𝟙 Z ≫ c) = p) :
    a ≫ (((b ≫ 𝟙 Z) ≫ c) ≫ d) = p ≫ d := by
  simpa only [Category.comp_id, Category.id_comp, Category.assoc] using
    congrArg (fun t => t ≫ d) h
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：元始域への制限後の全 shifted 左軸は元左関手の Yoneda shift。
方針：元全 cone 左軸と同じ実 shift の全 Hom 作用を使用する。
規約：元全関手の等号。使われ方：元二重 shift の全逆回転右軸回収。 -/
lemma dgIdentityHomGluingShiftedLeftAxis :
    (H).comp (dgHomGluingShiftedLeftModuleFunctor R C C C (I) (I)) =
      (F.comp (dgYoneda R C)).comp (moduleShiftDG R C 1) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (H).comp (dgHomGluingShiftedLeftModuleFunctor R C C C (I) (I)))
    (G := (F.comp (dgYoneda R C)).comp (moduleShiftDG R C 1)) (fun _ => rfl)
  intro x y
  exact postIdentityShift _ _ _ _ _ (dgIdentityHomGluingFunctor_coneLeftMap R C F G a h x y)
end SerrePositivity.KST.SConstruction
