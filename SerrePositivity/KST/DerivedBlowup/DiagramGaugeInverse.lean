module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeFunctor

/-!
概要：KST §3.1 の Hom 重み付けの逆と合成を dg 関手の等式として扱う。
方針：指定 Hom 同型を逆にし、元の合成可換式を同型の消去で移す。
規約：対象を固定する既存の係数 dg 圏上で構成する。
使われ方：大域捻りの可逆性と整数指数の加法整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：Hom gauge は指定した全 Hom 同型で決まる。
方針：構造体の他の欄は命題なので証明の一意性で消去する。
規約：KST §3.1。使われ方：整数冪の公式を大域の関手等式へ移す。 -/
theorem DiagramHomGauge.ext (s t : DiagramHomGauge F)
    (h : ∀ (i j : J) (hij : i ≤ j), s.scale hij = t.scale hij) : s = t := by
  cases s with
  | mk ss si sc =>
    cases t with
    | mk ts ti tc =>
      have he : @ss = @ts := by funext i j hij; exact h i j hij
      cases he
      rfl

/-- 概要：証明済み Hom gauge の指定逆 gauge。
方針：tensor の逆同型と合成先の逆同型で元の合成式を消去する。
規約：KST §3.1。使われ方：捻りの逆 dg 関手。 -/
def DiagramHomGauge.inverse (s : DiagramHomGauge F) : DiagramHomGauge F where
  scale h := (s.scale h).symm
  scale_id i := by rw [s.scale_id]; rfl
  scale_comp h g := by
    apply (cancel_mono (s.scale (h.trans g)).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
    rw [← s.scale_comp h g, ← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id, id_tensorHom_id, Category.id_comp]

variable [DecidableLE J]

/-- 概要：恒等 gauge による dg 自己関手は恒等関手。
方針：包含上の Hom 同定とその逆を消去し、非包含では定義を読む。
規約：KST §3.1。使われ方：零捻りの大域作用。 -/
theorem diagramGaugeDGFunctor_identity :
    diagramGaugeDGFunctor F (diagramHomGaugeIdentity F) =
      DGFunctor.id (DiagramModuleCoefficientObject F) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change (diagramGaugeHomIso F (diagramHomGaugeIdentity F) x.index y.index).hom = 𝟙 _
  by_cases h : x.index ≤ y.index
  · simp only [diagramGaugeHomIso, dite_eq_left h, diagramHomGaugeIdentity,
      Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id]
  · simp only [diagramGaugeHomIso, dite_eq_right h, Iso.refl_hom]

/-- 概要：二つの gauge の合成は指定 dg 自己関手の合成に一致する。
方針：包含上の Hom 同定の中間の順逆を消去する。
規約：KST §3.1。使われ方：捻りの和と逆を実際の作用へ移す。 -/
theorem diagramGaugeDGFunctor_comp (s t : DiagramHomGauge F) :
    (diagramGaugeDGFunctor F s).comp (diagramGaugeDGFunctor F t) =
      diagramGaugeDGFunctor F (s.comp F t) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change (diagramGaugeHomIso F s x.index y.index).hom ≫
      (diagramGaugeHomIso F t x.index y.index).hom =
    (diagramGaugeHomIso F (s.comp F t) x.index y.index).hom
  by_cases h : x.index ≤ y.index
  · simp only [diagramGaugeHomIso, dite_eq_left h, DiagramHomGauge.comp,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  · simp only [diagramGaugeHomIso, dite_eq_right h, Iso.refl_hom, Category.id_comp]

/-- 概要：逆 gauge の各 Hom 同型は元の Hom 同型の逆。
方針：包含上の指定同定の共役を逆にし、非包含では恒等の逆を読む。
規約：KST §3.1。使われ方：逆 dg 自己関手の合成計算。 -/
theorem diagramGaugeHomIso_inverse (s : DiagramHomGauge F) (i j : J) :
    diagramGaugeHomIso F (s.inverse F) i j = (diagramGaugeHomIso F s i j).symm := by
  by_cases h : i ≤ j
  · simp only [diagramGaugeHomIso, dite_eq_left h, DiagramHomGauge.inverse,
      Iso.trans_symm, Iso.trans_assoc]
    rfl
  · simp only [diagramGaugeHomIso, dite_eq_right h, Iso.refl_symm]

/-- 概要：gauge の dg 自己関手に指定逆を続けると恒等関手。
方針：対象は固定され、各 Hom では指定同型と逆同型を消去する。
規約：KST §3.1。使われ方：大域捻り作用の可逆性。 -/
theorem diagramGaugeDGFunctor_inverse_comp (s : DiagramHomGauge F) :
    (diagramGaugeDGFunctor F s).comp (diagramGaugeDGFunctor F (s.inverse F)) =
      DGFunctor.id (DiagramModuleCoefficientObject F) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change (diagramGaugeHomIso F s x.index y.index).hom ≫
      (diagramGaugeHomIso F (s.inverse F) x.index y.index).hom = 𝟙 _
  rw [diagramGaugeHomIso_inverse]
  exact Iso.hom_inv_id _

/-- 概要：指定逆の dg 自己関手に元の gauge を続けても恒等関手。
方針：各 Hom の逆同型と順同型を消去する。
規約：KST §3.1。使われ方：捻り作用の両側逆。 -/
theorem diagramGaugeDGFunctor_comp_inverse (s : DiagramHomGauge F) :
    (diagramGaugeDGFunctor F (s.inverse F)).comp (diagramGaugeDGFunctor F s) =
      DGFunctor.id (DiagramModuleCoefficientObject F) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change (diagramGaugeHomIso F (s.inverse F) x.index y.index).hom ≫
      (diagramGaugeHomIso F s x.index y.index).hom = 𝟙 _
  rw [diagramGaugeHomIso_inverse]
  exact Iso.inv_hom_id _

end SerrePositivity.KST.DerivedBlowup
