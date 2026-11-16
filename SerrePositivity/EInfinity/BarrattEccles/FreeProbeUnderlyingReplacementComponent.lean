module
public import SerrePositivity.EInfinity.BarrattEccles.AlgebraReplacementUnderlyingComponent
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeDerivedUnitEndpointRecovery
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeUnitWeak
/-!
概要：既存の自由 probe の全忘却比較を元の置換 augmentation で回収する。
方針：同じ全源同型の評価と cofibrant 置換射の正方形を接続する。
規約：既存の標準単位・元の単位・同じ端点同型を保持する。
使われ方：局所化源での単位比較の弱同値性を標準単位へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom ComplexLimits _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A)

private lemma mappedTransportArrow {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) {a b c : C} {d : D} (h : a = b) (f : b ⟶ c)
    (g : a ⟶ c) (k : T.obj c ⟶ d) (hg : g = eqToHom h ≫ f) :
    Arrow.mk (T.map g ≫ k) = Arrow.mk (T.map f ≫ k) := by
  rw [hg, Functor.map_comp, eqToHom_map, Category.assoc]
  exact Arrow.arrow_mk_eqToHom_comp _ _

private lemma chosenTransportArrow {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ D) {a b c : C} {d d' e : D} (p : a ≅ b) (q : a ≅ c)
    (r : T.obj c ≅ d) (s : T.obj a ≅ e) (t : e ≅ d')
    (h : Arrow.mk (T.map q.hom ≫ r.hom) = Arrow.mk (s.hom ≫ t.hom)) :
    Arrow.mk (T.map (p.symm ≪≫ q).hom ≫ r.hom) =
      Arrow.mk ((T.mapIso p).symm ≪≫ s ≪≫ t).hom := by
  have hh := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq (T.map p.inv) _ (T.map p.inv) _ rfl h
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_inv,
    Category.assoc] using hh

private lemma chosenVertexTransportArrow {C D : SSet.{u}} (U : C ⟶ D)
    {a b c : C.obj (Opposite.op ⦋0⦌)}
    {d d' z : D.obj (Opposite.op ⦋0⦌)} (p : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b) (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a c)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (U.app (Opposite.op ⦋0⦌) c) d)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (U.app (Opposite.op ⦋0⦌) a) z) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z d')
    (h : Arrow.mk ((hoFunctor.map U).toFunctor.map q.hom ≫ r.hom) =
      Arrow.mk (s.hom ≫ t.hom)) :
    Arrow.mk ((hoFunctor.map U).toFunctor.map (p.symm ≪≫ q).hom ≫ r.hom) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map p U).symm ≪≫ s ≪≫ t).hom := by
  exact chosenTransportArrow (hoFunctor.map U).toFunctor p q r s t h

private lemma chosenFullFunctorTransportArrow {L C D : SSet.{u}}
    (F : L ⟶ C) (U : C ⟶ D) {V : L ⟶ D} (x : L.obj (Opposite.op ⦋0⦌))
    {b c : C.obj (Opposite.op ⦋0⦌)} {d d' : D.obj (Opposite.op ⦋0⦌)}
    (p : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) x) b)
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app (Opposite.op ⦋0⦌) x) c)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (U.app (Opposite.op ⦋0⦌) c) d)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ U) V) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (V.app (Opposite.op ⦋0⦌) x) d')
    (h : Arrow.mk ((hoFunctor.map U).toFunctor.map q.hom ≫ r.hom) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate s.hom x ≫ t.hom)) :
    Arrow.mk ((hoFunctor.map U).toFunctor.map (p.symm ≪≫ q).hom ≫ r.hom) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map p U).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate s x ≪≫ t).hom := by
  refine chosenVertexTransportArrow U p q r (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate s x) t ?_
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate]
  exact h

private lemma vertexIso_hom_arrow {D : SSet.{u}}
    {a b : D.obj (Opposite.op ⦋0⦌)} {e e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b} (h : e = e') :
    Arrow.mk e.hom = Arrow.mk e'.hom :=
  congrArg (fun i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b => Arrow.mk i.hom) h

private lemma vertexIso_map_hom_comp_arrow {C D : SSet.{u}} (U : C ⟶ D)
    {a b : C.obj (Opposite.op ⦋0⦌)} {d : D.obj (Opposite.op ⦋0⦌)}
    {e e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b} (h : e = e')
    (k : (HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) b) : hoFunctor.obj D) ⟶
      HomotopyCategory.mk d) :
    Arrow.mk ((hoFunctor.map U).toFunctor.map e.hom ≫ k) =
      Arrow.mk ((hoFunctor.map U).toFunctor.map e'.hom ≫ k) :=
  congrArg (fun i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso a b =>
    Arrow.mk ((hoFunctor.map U).toFunctor.map i.hom ≫ k)) h

private lemma relativeChosenIso_def : freeProbeRelativeChosenSourceIso A X =
    (freeProbeCAlgSource_vertexIso A X).symm ≪≫ freeProbeRelativeFullSourceIso A X := rfl

private lemma derivedUnderlyingIso_def : freeProbeDerivedUnitUnderlyingVertexIso A X =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (freeProbeCAlgSource_vertexIso A X) (cAlgForgetDerived A)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate (freeProbeUnderlyingDerivedSourceIso A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≪≫
        complexDiagramDerivedVertexIso A
          (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X := rfl

private lemma hom_comp_arrow_congr {C : Type*} [Category* C] {a b c : C}
    {f g : a ⟶ b} (h : f = g) (k : b ⟶ c) : Arrow.mk (f ≫ k) = Arrow.mk (g ≫ k) :=
  congrArg (fun v : a ⟶ b => Arrow.mk (v ≫ k)) h

private lemma relativeUnitHom_def : freeProbeRelativeUnitHom A X =
    freeProbeUnitOrdinaryHom A X ≫
      (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).inv := rfl

private lemma unitEndpointArrowCancel {C : Type*} [Category* C]
    {a b c d e f : C} (p : a ≅ b) (v : b ⟶ c) (w : c ⟶ d) (k : d ≅ e)
    (z : c ≅ f) (n : a ⟶ f) (m : a ⟶ d)
    (hw : Arrow.mk (w ≫ k.hom) = Arrow.mk z.hom)
    (hn : p.hom ≫ v ≫ z.hom = n) (hm : Arrow.mk (m ≫ k.hom) = Arrow.mk n) :
    p.hom ≫ v ≫ w = m := by
  have hc := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq (p.hom ≫ v) _ (p.hom ≫ v) _ rfl hw
  have hc' : Arrow.mk ((p.hom ≫ v ≫ w) ≫ k.hom) = Arrow.mk n := by
    simpa only [Category.assoc, hn] using hc
  exact (cancel_mono k.hom).mp ((Arrow.mk_injective _ _) (hc'.trans hm.symm))

private lemma unitTransportCancel {C : Type*} [Category* C] {a b c : C}
    (e : b ≅ c) (f : a ⟶ c) : (f ≫ e.inv) ≫ e.hom = f := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：元の全自由源の忘却比較は同じ置換頂点比較と augmentation の合成。
方針：同じ自由関手による前合成の評価と全代数源比較を使う。
規約：元の全比較を保持。使われ方：標準単位の自由側の端点回収。 -/
lemma freeProbeUnderlyingDerivedSourceIso_component_arrow :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnderlyingDerivedSourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) =
    Arrow.mk ((cofibrantForgetOrdinaryVertexIso A
        ((cofibrantAlgebraReplacement A).obj (freeProbeElementCofibrantSource A X).obj)).hom ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk
          (framedLimitProbeComparison A (freeProbeElementCofibrantSource A X).obj).hom).map
          (complexOrdinaryDerivedSource A)).toTruncated) := by
  let e := (algebraCAlgSource_underlyingDerivedIso A).precomp (nerveMap (freeProbeFunctor A))
  have he : nerveMap (freeProbeFunctor A) ≫ algebraUnderlyingDerivedSource A =
      nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
        complexOrdinaryDerivedSource A := by
    rw [algebraUnderlyingDerivedSource, ← Category.assoc, freeProbeUnderlyingNerve_eq]
  have hd : freeProbeUnderlyingDerivedSourceIso A = e ≪≫
      eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) he) := rfl
  rw [hd, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate_eqToIso_hom he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)]
  refine (Arrow.arrow_mk_comp_eqToHom _ _).trans ?_
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIsoEvaluate_precomp_arrow (algebraCAlgSource_underlyingDerivedIso A)
    (nerveMap (freeProbeFunctor A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)
  have hv : (nerveMap (freeProbeFunctor A)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeElementCofibrantSource A X).obj := ComposableArrows.ext₀ rfl
  have hv' := congrArg (fun v => (Arrow.mk
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (algebraCAlgSource_underlyingDerivedIso A).hom v) :
      Arrow (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)))) hv
  exact (hs.trans hv').trans
    (algebraCAlgSource_underlyingDerivedIso_component_arrow A
      (freeProbeElementCofibrantSource A X).obj)

/-- 概要：元の自由源の置換頂点比較の U 像は同じ置換 augmentation の導来像。
方針：同じ実置換射に全源比較の成分正方形を適用する。
規約：元の局所化成分辺を保持。使われ方：全自由源比較との照合。 -/
lemma freeProbeRelativeFullSourceIso_forget_ordinary_arrow :
    Arrow.mk ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (freeProbeRelativeFullSourceIso A X).hom ≫
      (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom) =
    Arrow.mk ((cofibrantForgetOrdinaryVertexIso A
        ((cofibrantAlgebraReplacement A).obj (freeProbeElementCofibrantSource A X).obj)).hom ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk
          (framedLimitProbeComparison A (freeProbeElementCofibrantSource A X).obj).hom).map
          (complexOrdinaryDerivedSource A)).toTruncated) := by
  refine (mappedTransportArrow (hoFunctor.map (cAlgForgetDerived A)).toFunctor
    (congrArg HomotopyCategory.mk (freeProbeCAlgSource_relativeReplacement_vertex A X))
    _ _ _ (freeProbeRelativeFullSourceIso_hom A X)).trans ?_
  exact cofibrantReplacement_forget_ordinary_arrow A (freeProbeElementCofibrantSource A X)

/-- 概要：同じ自由源頂点比較の U 像は元の全忘却比較の評価と一致する。
方針：両経路を同じ置換 augmentation の全 Arrow に回収して反映する。
規約：元の全源同型と成分辺を保持。使われ方：標準単位と局所化源単位の整合。 -/
lemma freeProbeRelativeFullSourceIso_forget_underlying_arrow :
    Arrow.mk ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (freeProbeRelativeFullSourceIso A X).hom ≫
      (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnderlyingDerivedSourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      (complexDiagramDerivedVertexIso A
        (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X).hom) := by
  have hd : Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnderlyingDerivedSourceIso A).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫ (complexDiagramDerivedVertexIso A
          (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X).hom) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (freeProbeUnderlyingDerivedSourceIso A).hom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) := by
    exact complexDiagramDerivedVertexIso_comp_arrow A
      (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X _
  exact (freeProbeRelativeFullSourceIso_forget_ordinary_arrow A X).trans
    (hd.trans (freeProbeUnderlyingDerivedSourceIso_component_arrow A X)).symm

/-- 概要：選択済み自由頂点からの比較は同じ標準単位の忘却端点比較と整合する。
方針：既存の自由源頂点比較を相殺し、元の全源比較の評価へ戻す。
規約：選択済み頂点と比較射を保持。使われ方：標準単位の端点輸送。 -/
lemma freeProbeRelativeChosenSourceIso_forget_underlying_arrow :
    Arrow.mk ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (freeProbeRelativeChosenSourceIso A X).hom ≫
      (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom) =
    Arrow.mk (freeProbeDerivedUnitUnderlyingVertexIso A X).hom := by
  refine (vertexIso_map_hom_comp_arrow (cAlgForgetDerived A) (relativeChosenIso_def A X)
    (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom).trans ?_
  exact (chosenFullFunctorTransportArrow
    (V := nerveMap (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) ≫
      complexOrdinaryDerivedSource A)
    (freeProbeCAlgSource A) (cAlgForgetDerived A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) (freeProbeCAlgSource_vertexIso A X) (freeProbeRelativeFullSourceIso A X)
    (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X))
    (freeProbeUnderlyingDerivedSourceIso A)
    (complexDiagramDerivedVertexIso A
      (freeProbeFunctor A ⋙ Operad.Algebra.forget (operad A)) X)
    (freeProbeRelativeFullSourceIso_forget_underlying_arrow A X)).trans
      (vertexIso_hom_arrow (derivedUnderlyingIso_def A X)).symm

/-- 概要：既存の標準単位を同じ源頂点同型で輸送すると元の局所化源単位になる。
方針：標準単位の端点回収式と同じ置換比較の忘却正方形を接続する。
規約：標準単位を選び直さない。使われ方：標準単位比較自身の弱同値性。 -/
lemma freeProbeRelativeChosenSourceIso_unit_triangle :
    (complexProbeDerivedSourceVertexIso A X).hom ≫ freeProbeDerivedUnitComponent A X ≫
      (hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (freeProbeRelativeChosenSourceIso A X).hom = freeProbeRelativeUnitHom A X := by
  refine unitEndpointArrowCancel (complexProbeDerivedSourceVertexIso A X)
    (freeProbeDerivedUnitComponent A X)
    ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
      (freeProbeRelativeChosenSourceIso A X).hom)
    (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X))
    (freeProbeDerivedUnitUnderlyingVertexIso A X) (freeProbeUnitOrdinaryHom A X)
    (freeProbeRelativeUnitHom A X)
    (freeProbeRelativeChosenSourceIso_forget_underlying_arrow A X)
    (freeProbeDerivedUnitComponent_recovery A X) ?_
  refine (hom_comp_arrow_congr (relativeUnitHom_def A X)
    (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).hom).trans ?_
  exact congrArg Arrow.mk
    (unitTransportCancel (cofibrantForgetOrdinaryVertexIso A
      (freeProbeElementCofibrantSource A X)) (freeProbeUnitOrdinaryHom A X))

end SerrePositivity.EInfinity.BarrattEccles
