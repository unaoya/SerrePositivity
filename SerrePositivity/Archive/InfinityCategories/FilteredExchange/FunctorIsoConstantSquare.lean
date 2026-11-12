module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
概要：恒等な図式成分と等式からの図式同型を指定比較の自然性の式から消去する。
方針：恒等成分の等式と指定同型の型付きの一致を同時に消去する。
規約：脚の比較の値を保持。使われ方：全空間引き戻し錐の自然性の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値な図式に沿う指定比較の自然性は元の脚の三角形の可換式へ戻る。
方針：恒等成分と等式からの同型を消去。
規約：指定された脚の比較を別の同型で置き換えない。使われ方：二次の整合性。 -/
lemma functorIso_constant_square {X Y Z : SSet.{u}}
    {ui vi : X ⟶ Y} {uj vj : X ⟶ Z} (m : Y ⟶ Z) (ri : Y ⟶ Y) (rj : Z ⟶ Z)
    (n : FunctorIso uj (ui ≫ m)) (t : FunctorIso vj (vi ≫ m))
    (ei : FunctorIso (ui ≫ ri) vi) (ej : FunctorIso (uj ≫ rj) vj)
    (q : FunctorIso (m ≫ rj) (ri ≫ m))
    (ei' : FunctorIso ui vi) (ej' : FunctorIso uj vj)
    (hi : ri = 𝟙 Y) (hj : rj = 𝟙 Z) (hq : IsFunctorEqIso q)
    (hei : HEq ei' ei) (hej : HEq ej' ej)
    (h : n.postcomp rj ≪≫ q.precomp ui ≪≫ ei.postcomp m = ej ≪≫ t) :
    n ≪≫ ei'.postcomp m = ej' ≪≫ t := by
  subst ri
  subst rj
  change FunctorIso ui vi at ei
  change FunctorIso uj vj at ej
  change FunctorIso m m at q
  change n.postcomp (𝟙 Z) ≪≫ q.precomp ui ≪≫ ei.postcomp m = ej ≪≫ t at h
  have hi' : ei' = ei := eq_of_heq hei
  have hj' : ej' = ej := eq_of_heq hej
  subst ei'
  subst ej'
  have hq' : q = Iso.refl _ := hq.eq rfl
  rw [hq', functorIso_precomp_eq_mapIso, Functor.mapIso_refl] at h
  let eiM : FunctorIso (ui ≫ m) (vi ≫ m) := ei.postcomp m
  change n.postcomp (𝟙 Z) ≪≫
    (show FunctorIso (ui ≫ m) (ui ≫ m) from Iso.refl _) ≪≫ eiM = ej ≪≫ t at h
  have h' := (congrArg (fun e : FunctorIso uj (ui ≫ m) =>
    e ≪≫ (show FunctorIso (ui ≫ m) (ui ≫ m) from Iso.refl _) ≪≫ eiM)
      (functorIso_postcomp_id n)).symm.trans h
  exact (congrArg (fun e : FunctorIso (ui ≫ m) (vi ≫ m) => n ≪≫ e)
    (Iso.refl_trans eiM)).symm.trans h'

end SerrePositivity.InfinityCategories.F2
