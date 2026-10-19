module
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaExact
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaNerveIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGUniverseLiftFunctor

/-! # 共通宇宙の前三角 dg 関手の完全性

概要：前三角 dg 圏間の dg 関手の対象宇宙を上げた native nerve は完全。
方針：全加群への延長の完全性、Yoneda 比較の実関手同型、押し出しの反映を使う。
規約：全 cofiber 列の保存を証明。使われ方：元の宇宙の商関手の完全性への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A D E)

omit [Small.{u} D] in
/-- 共通宇宙の関手と Yoneda の合成は、元の対象像の Yoneda と厳密に一致。 -/
lemma dgUniverseLiftFunctor_comp_yoneda :
    (dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F).comp
        ((dgUniverseLiftDown A E).comp (dgYoneda A E)) =
      (dgUniverseLiftDown A D).comp (F.comp (dgYoneda A E)) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, dgUniverseLiftFunctor, dgUniverseLiftDown,
    dgObjectImageEvaluation, Category.id_comp, Category.comp_id, eqToHom_refl]

/-- 加群値の対象像の Yoneda は、前三角始域において完全。 -/
lemma dgPretriangulatedFunctorYoneda_isExactFunctor [IsDGPretriangulated A D] :
    IsExactFunctor (dgNerve.map ((dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp
      (F.comp (dgYoneda A E)))) := by
  let := dgPretriangulatedYoneda_isExactFunctor A D
  let := dgModuleFunctorNerve_isExactFunctor A D E (dgModuleExtension A D E F)
  exact isExactFunctor_of_functorIso (dgModuleExtensionYonedaCompositeIso A D E F)

/-- 前三角 dg 圏間の dg 関手の共通宇宙の native nerve は完全。 -/
theorem dgPretriangulatedFunctorLifted_isExactFunctor
    [IsDGPretriangulated A D] [IsDGPretriangulated A E] :
    IsExactFunctor (dgNerve.map
      (dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F)) where
  preservesZero := dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    apply dgPretriangulatedYoneda_reflectsPushoutSquare A E
    have h := dgPretriangulatedFunctorYoneda_isExactFunctor A D E F
    rw [← dgUniverseLiftFunctor_comp_yoneda A D E F, dgNerve.map_comp] at h
    let := h
    have hc := IsExactFunctor.preservesCofiber
      (F := dgNerve.map
        (dgUniverseLiftFunctor.{u, v, v, max (u + 1) v, max (u + 1) v} F) ≫
          dgNerve.map ((dgUniverseLiftDown A E).comp (dgYoneda A E))) t ht
    simpa only [IsCofiberSequence, ZeroTriangle.map, Category.assoc] using hc

end SerrePositivity.InfinityCategories
