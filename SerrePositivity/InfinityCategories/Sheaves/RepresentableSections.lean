module

public import SerrePositivity.InfinityCategories.Sheaves.SectionsOf

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointConeLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.PointJoinNerveExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SimplexConeRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSections
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsDiagram

/-!
概要：集合重みの指定切断錐を、元の篩の制限錐へ接続する。
方針：既存のG8の射と錐の普遍性を使い、全錐の再添字を照合する。
  文献対応：HTT 6.2.2.6、Kerodon §7.1（Tag 02H1）の層条件の切断表示。
規約：元の指定錐・比較辺を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {𝒞 : Type u} [SmallCategory 𝒞] {E : SSet.{u+1}} [Quasicategory E]

/-- 表現可能前層の元の圏の恒等射による指定錐。 -/
def representableElementsCone (U : 𝒞) : Cone (Functor.Elements.π (yoneda.obj U)) where
  pt := Opposite.op U
  π :=
    { app := fun x => x.val.op
      naturality := by
        intro x y f
        change 𝟙 (Opposite.op U) ≫ y.val.op = x.val.op ≫ f.hom
        rw [Category.id_comp, ← f.map_val]
        rfl }

/-- 標準錐の篩への制限は、S1 の錐そのもの。 -/
lemma representableElementsCone_sieve {U : 𝒞} (S : Sieve U) :
    (representableElementsCone U).whisker
      (sieveCategoryToElements S ⋙ S.functorInclusion.mapElements) = sieveCone S := by
  rfl

/-- F(U) を頂点とする、表現可能重み上の指定錐。 -/
def representableSectionsCone (U : 𝒞) (F : Presheaf 𝒞 E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (sectionsOfDiagram (yoneda.obj U) F) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (representableElementsCone U)).ulift).postcomp F

lemma representableSectionsCone_vertex (U : 𝒞) (F : Presheaf 𝒞 E) :
    (representableSectionsCone U F).vertex =
      F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))) := by
  rw [representableSectionsCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_postcomp,
    SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_vertex]
  rfl

/-- 元の圏の始対象 (U,id) を、大きい宇宙の点として指定する。 -/
def representableSectionsInitialPoint (U : 𝒞) :
    (Δ[0] : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (yoneda.obj U).Elements) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (AsSmall.up.obj (Functor.Elements.initialYonedaObj U)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso (yoneda.obj U).Elements).inv

lemma representableSectionsInitialPoint_eq (U : 𝒞) :
    representableSectionsInitialPoint U = SSet.yonedaEquiv.symm
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Functor.Elements.initialYonedaObj U))) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso (yoneda.obj U).Elements).hom).mp
  rw [representableSectionsInitialPoint, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso_vertex
      (yoneda.obj U).Elements (Functor.Elements.initialYonedaObj U)).symm

/-- 始対象の点への制限は、サイズを上げても left anodyne。
AsSmall の通常圏に移してから既存の始対象定理を使う。 -/
lemma representableSectionsInitialPoint_leftAnodyne (U : 𝒞) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (representableSectionsInitialPoint U) := by
  letI : (AsSmall.up : (yoneda.obj U).Elements ⥤ AsSmall.{u + 1} (yoneda.obj U).Elements).IsEquivalence :=
    (AsSmall.equiv (C := (yoneda.obj U).Elements)).isEquivalence_functor
  have hi : IsInitial (AsSmall.up.obj (Functor.Elements.initialYonedaObj U) :
      AsSmall.{u + 1} (yoneda.obj U).Elements) :=
    (Functor.Elements.isInitialYonedaObj U).isInitialObj AsSmall.up
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne hi)
    (MorphismProperty.of_isIso _ _)

/-- 恒等射の点への制限は、表現可能標準錐の全射として定値。
F を適用する前の nerve で両端と唯一の混合辺を照合する。 -/
lemma representableSectionsCone_point_val (U : 𝒞) (F : Presheaf 𝒞 E) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (representableSectionsCone U F)
      (representableSectionsInitialPoint U)).val =
      SSet.const (F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))) := by
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (representableElementsCone U)).ulift
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (representableSectionsInitialPoint U) ≫ c.val =
      SSet.const (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U))) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso 𝒞ᵒᵖ).hom).mp
    rw [SSet.const_comp]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointJoinNerve_hom_ext
    · apply SSet.yonedaEquiv.injective
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso 𝒞ᵒᵖ).hom.app _ c.vertex = _
      rw [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_vertex]
      rfl
    · apply SSet.yonedaEquiv.injective
      rw [representableSectionsInitialPoint_eq]
      apply ComposableArrows.ext₀
      rfl
    · rw [representableSectionsInitialPoint_eq]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone (representableElementsCone U)).val.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex (Functor.Elements.initialYonedaObj U)) ⋙ AsSmall.up = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveCone_leg]
      refine ComposableArrows.ext₁ rfl rfl ?_
      simp [representableElementsCone, Functor.Elements.initialYonedaObj]
      change 𝟙 _ = AsSmall.up.{u, u, u + 1}.map (𝟙 (Opposite.op U))
      simp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (representableSectionsInitialPoint U) ≫ (c.val ≫ F) = _
  rw [← Category.assoc, hc, SSet.const_comp]

/-- 始対象 (U,id) の脚は恒等射なので、この指定錐が極限錐になる。 -/
lemma representableSectionsCone_isLimit (U : 𝒞) (F : Presheaf 𝒞 E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (representableSectionsCone U F) := by
  letI : Mono (representableSectionsInitialPoint U) := by
    unfold representableSectionsInitialPoint
    infer_instance
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_leftAnodyne (representableSectionsCone U F)
    (representableSectionsInitialPoint U) (representableSectionsInitialPoint_leftAnodyne U)).mp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.pointCone_isLimit_of_constant _ _ (representableSectionsCone_point_val U F)

/-- S8 の公開名を保持。選んだ極限錐と上の標準錐を、錐全体で比較する。 -/
def sectionsOf_representable (U : 𝒞) (F : Presheaf 𝒞 E)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (sectionsOfDiagram (yoneda.obj U) F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (sectionsOf (yoneda.obj U) F h)
      (F.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op U)))) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso (sectionsOfCone (yoneda.obj U) F h)
    (representableSectionsCone U F) (sectionsOfCone_isLimit _ _ _)
    (representableSectionsCone_isLimit U F)
  simpa only [sectionsOf, representableSectionsCone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso] using e


end SerrePositivity.InfinityCategories.Sheaves
