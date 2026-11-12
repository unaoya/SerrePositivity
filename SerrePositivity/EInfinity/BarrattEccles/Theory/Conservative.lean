module

public import SerrePositivity.EInfinity.BarrattEccles.Theory
public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy
public import SerrePositivity.EInfinity.ComplexLimits.StrictHomology
public import SerrePositivity.EInfinity.SimplicialLocalization.SourceHom
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebraLocalization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# Barratt–Eccles の忘却関手は保存的

## 概要
HA §3.2.2 の忘却関手の保存性を、既存の CAlg_R と D(R) の模型で示す。

## 方針
局所化の辺を cofibrant–fibrant な代数間の厳密射で代表し、
底の全次数のホモロジーで判定する。

## 規約
構成済みの Barratt–Eccles モデル構造だけを局所的に使う。

## 使われ方
Barratt–Eccles 実例の `forget_conservative`。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ComplexLimits SimplicialLocalization
open scoped Simplicial

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- DK 入力の通常の局所化では、厳密射からの写像は全射。 -/
lemma cofibrantAlgebraDK_Q_map_surjective
    (X Y : (cofibrantAlgebraRelativeCategory A).category) :
    Function.Surjective ((cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.map :
      (X ⟶ Y) → _) := by
  let := modelCategory A
  let D := cofibrantAlgebraInclusion A
  let W := cofibrantAlgebraWeakEquivalences A
  let Q := (weakEquivalences (operad A).Algebra).Q
  let E := cofibrantAlgebraHoEquivalence A
  let i := cofibrantAlgebraInclusionLocalizedIso A
  let UL := ULiftHom.down (C := CofibrantAlgebra A)
  let X' := UL.obj X
  let Y' := UL.obj Y
  let e := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv W X Y).trans
    (E.fullyFaithfulFunctor.homEquiv.trans ((Iso.homCongr (i.app X') (i.app Y')).symm))
  have hX : IsCofibrant (D.obj X') := X'.property
  have hY : IsFibrant (D.obj Y') := BarrattEccles.isFibrant A (D.obj Y')
  intro g
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization Q (D.obj X') (D.obj Y') (e g)
  let k : X ⟶ Y := ULift.up (ObjectProperty.homMk f)
  refine ⟨k, e.injective ?_⟩
  change (i.app X').hom ≫ E.functor.map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv W X Y
      ((cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.map k)) ≫
      (i.app Y').inv = e g
  have hmap : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv W X Y
      ((cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.map k) =
      W.Q.map (UL.map k) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ULiftRelativeLocalization.homEquiv_map W k
  have h := NatIso.naturality_2 i (UL.map k)
  change (i.app X').hom ≫ E.functor.map (W.Q.map (UL.map k)) ≫ (i.app Y').inv = Q.map f at h
  exact (congrArg (fun z => (i.app X').hom ≫ E.functor.map z ≫ (i.app Y').inv) hmap).trans
    (h.trans hf)

/-- 厳密複体の導来像が可逆なら、元の写像は擬同型。 -/
lemma complexOrdinaryDerivedSource_reflects_quasiIso {X Y : Complex A} (f : X ⟶ Y)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).toTruncated) :
    QuasiIso f := by
  let B := ordinaryToHoNerve (Complex A)
  let L := hoMap (complexOrdinaryDerivedSource A)
  have hL : IsIso (L.map (B.map f)) := h
  refine (quasiIso_iff f).mpr (fun i => (quasiIsoAt_iff_isIso_homologyMap f i).mpr ?_)
  let H := cohomologyOnHo A i
  let K := HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i
  let e : B ⋙ L ⋙ H ≅ K := complexOrdinaryDerivedSourceHomologyIso A i
  have hm : IsIso ((B ⋙ L ⋙ H).map f) := H.map_isIso (L.map (B.map f))
  have hn := NatIso.naturality_2 e.symm f
  have hi : IsIso ((e.app X).inv ≫ (B ⋙ L ⋙ H).map f ≫ (e.app Y).hom) := inferInstance
  change IsIso (K.map f)
  exact hn ▸ hi

/-- 局所化に送った厳密射の忘却像が可逆なら、元の射は指定弱同値。 -/
lemma cAlgLocalizationSource_map_reflects_weak
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y)
    (h : IsIso ((hoMap (cAlgForgetDerived A)).map
      ((hoMap (cAlgLocalizationSource A)).map (SSet.HomotopyCategory.homMk (nerve.edgeMk f))))) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences f := by
  apply (cofibrantAlgebraRelativeCategory_weakEquivalences_iff A f).mpr
  change QuasiIso ((cofibrantAlgebraDKForget A).map f)
  let φ := (cofibrantAlgebraDKForget A).map f
  let G := cofibrantAlgebraUnderlyingDerivedSource A
  let L := cAlgLocalizationSource A
  let U := cAlgForgetDerived A
  let a := SSet.HomotopyCategory.homMk (nerve.edgeMk f)
  have hcomp : hoMap (L ≫ U) = hoMap L ⋙ hoMap U :=
    congrArg Cat.Hom.toFunctor (hoFunctor.map_comp L U)
  have ha : IsIso ((hoMap (L ≫ U)).map a) := by
    rw [hcomp]
    exact h
  let η := (cAlgForgetDerived_sourceIso A).toNatIso
  have hn := NatIso.naturality_2 η.symm a
  have hc : IsIso ((η.app _).inv ≫ (hoMap (L ≫ U)).map a ≫ (η.app _).hom) := inferInstance
  have hg : IsIso ((hoMap G).map a) := hn ▸ hc
  have hg' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      ((nerve.edgeMk φ).map (complexOrdinaryDerivedSource A)).toTruncated := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      (e := ((nerve.edgeMk f).map G).toTruncated) ?_).mp hg
    change (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌)
      ((cofibrantAlgebraForgetNerve A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) =
      (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ φ)
    rw [cofibrantAlgebraForgetNerve_mk₁]
  exact complexOrdinaryDerivedSource_reflects_quasiIso A φ hg'


set_option maxHeartbeats 800000 in
-- CAlg_R の頂点を DK の対象で表示し直す二つの端点の型検査に既定値を超える。
/-- HA §3.2.2 の忘却関手は、可逆な辺を反映する。 -/
lemma cAlgForgetDerived_conservative {x y : (CAlg_R A) _⦋0⦌}
    (e : SSet.Edge x y) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      (e.map (cAlgForgetDerived A)).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := CAlg_R A) e.toTruncated := by
  obtain ⟨X, rfl⟩ := (cAlgVertexEquiv A).surjective x
  obtain ⟨Y, rfl⟩ := (cAlgVertexEquiv A).surjective y
  obtain ⟨f, hf⟩ := localizationStrictHom_represent (cofibrantAlgebraRelativeCategory A)
    (cofibrantAlgebraDK_Q_map_surjective A X Y) (SSet.HomotopyCategory.homMk e)
  let F := hoMap (cAlgForgetDerived A)
  let L := hoMap (cAlgLocalizationSource A)
  let a := SSet.HomotopyCategory.homMk (nerve.edgeMk f)
  let i := localizationStrictSourceIso (cofibrantAlgebraRelativeCategory A)
  have hn : L.map a ≫ (i Y).hom = (i X).hom ≫ SSet.HomotopyCategory.homMk e :=
    (localizationStrictSourceIso_naturality _ f).trans
      (congrArg (fun k => (i X).hom ≫ k) hf)
  have hn' := congrArg F.map hn
  simp only [Functor.map_comp] at hn'
  have he : IsIso (F.map (SSet.HomotopyCategory.homMk e)) := h
  have hh : IsIso (F.map (L.map a)) := by
    have hk : IsIso (F.map (L.map a) ≫ F.map (i Y).hom) := by
      rw [hn']
      infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map (i Y).hom)
  have hw := cAlgLocalizationSource_map_reflects_weak A f hh
  have hweak := cAlgLocalizationSource_inverts A
    (show ComposableArrows.mk₁ f ∈ weakNerveEdges _ from ⟨_, _, f, hw, rfl⟩)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := CAlg_R A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
    ((truncation 2).map (cAlgLocalizationSource A))) at hweak
  have hu : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := CAlg_R A)
      ((nerve.edgeMk f).map (cAlgLocalizationSource A)).toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := CAlg_R A) (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
      ((truncation 2).map (cAlgLocalizationSource A)))
      (f := ((nerve.edgeMk f).map (cAlgLocalizationSource A)).toTruncated) rfl).mp hweak
  have hu' : IsIso (L.map a) := hu
  have hk : IsIso ((i X).hom ≫ SSet.HomotopyCategory.homMk e) := by
    rw [← hn]
    infer_instance
  change IsIso (SSet.HomotopyCategory.homMk e)
  exact IsIso.of_isIso_comp_left (i X).hom (SSet.HomotopyCategory.homMk e)

end SerrePositivity.EInfinity.BarrattEccles
