module
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction
public import SerrePositivity.DifferentialGraded.Module.FreeSphere
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGUniverseLiftHomQuasiIso
/-!
概要：元の dg 関手の自由生成代表上の Hom 準同型性から全 Hom 準同型性を検出する。
方針：graph の射影的列で同じ Hom 写像を比較し、cone と retract による厚い帰納を使う。
規約：指定生成集合と実 dg 関手を保持し、H⁰ 充満忠実性を入力に追加しない。
使われ方：D-17。D2 の元の小 Perf 対角と任意の追加対象宇宙での生成判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w r s
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]

lemma dgFunctor_homQuasiIso_of_thickGenerators (F : DGFunctor R C D) (G : Set C)
    (hG : modulePerfectOver R C G = modulePerfect R C)
    (h : ∀ x ∈ G, ∀ y ∈ G, QuasiIso (F.map x y)) : HomQuasiIso F := by
  let P := functorGraph R C D F
  have hy (x y : C) : IsIso (yonedaHom R D (F.obj x) (F.obj y)) := by
    change IsIso (dgYonedaIso R (F.obj x) (representable R (F.obj y))).inv
    infer_instance
  have hp (x : C) : moduleHomotopicallyProjective R D
      (Morita.criterionPerfColumn R C D P x) :=
    representable_homotopicallyProjective R D (F.obj x)
  have hP : Morita.criterionPerfFullHomQuasiIso R C D P := by
    apply Morita.criterionPerfFullHomQuasiIso_of_generators R C D P G hG
    intro x hx y hy'
    rw [Morita.criterionPerfHomComparison_projective_iff R C D P x y (hp x)]
    change QuasiIso (F.map x y ≫ yonedaHom R D (F.obj x) (F.obj y))
    letI := h x hx y hy'
    letI := hy x y
    infer_instance
  intro x y
  have hxy := (Morita.criterionPerfHomComparison_projective_iff R C D P x y (hp x)).1 (hP x y)
  change QuasiIso (F.map x y ≫ yonedaHom R D (F.obj x) (F.obj y)) at hxy
  letI := hy x y
  letI := hxy
  exact quasiIso_of_comp_right _ (yonedaHom R D (F.obj x) (F.obj y))

lemma dgFunctor_homQuasiIso_of_singleThickGenerator (F : DGFunctor R C D) (b : C)
    (hb : modulePerfectOver R C {b} = modulePerfect R C)
    (h : QuasiIso (F.map b b)) : HomQuasiIso F := by
  apply dgFunctor_homQuasiIso_of_thickGenerators R C D F {b} hb
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst x
  subst y
  exact h

lemma dgUniverseLiftFunctor_homQuasiIso_of_thickGenerators (F : DGFunctor R C D) (G : Set C)
    (hG : modulePerfectOver R C G = modulePerfect R C)
    (h : ∀ x ∈ G, ∀ y ∈ G, QuasiIso (F.map x y)) :
    HomQuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, w, r, s} F) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_homQuasiIso_iff F).2
    (dgFunctor_homQuasiIso_of_thickGenerators R C D F G hG h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
