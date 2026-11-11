module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeBaseChangeComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.JointRealizationComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionBaseChangeComparison

/-!
概要：標準反復 pullback 比較を全相対切断の共同図式比較へ束ねる。
方針：元の全高次相対射の自然性と、添字の前合成の自然性を使う。
規約：元の pullback 合成同型と元の相対後合成を保持する。
使われ方：P-12 の指定共同切断底変換同型の合成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：固定始域からの切断の標準反復 pullback 比較は全 left fibrations 上で豊穣自然。
方針：元の高次相対射の底変換の三座標の自然性を各単体で使う。
規約：元の標準比較射を成分にする。使われ方：全切断図式の共同比較の各添字。 -/
def relativeBaseChangeCompEnrichedComparison {B D T : SSet.{u}}
    (k : D ⟶ B) (l : T ⟶ D) (a : Over T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched (l ≫ k)).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched l)).comp SSet
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation a)) := by
  refine ⟨fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeCompComparison p.val.hom k l a.hom, ?_⟩
  intro p q
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (pullback.snd p.val.hom (l ≫ k)) a.hom).obj n at s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom p.val.hom).obj n at t
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback (pullback.snd p.val.hom k)
      (pullback.snd q.val.hom k) l).app n
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p.val.hom q.val.hom k).app n t)).val.app m
          (α ≫ 𝟙 m))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeCompComparison p.val.hom k l a.hom).app n s).val.app m
        (α ≫ 𝟙 m) x) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeCompComparison q.val.hom k l a.hom).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a
        (Over.mk (pullback.snd p.val.hom (l ≫ k)))
        (Over.mk (pullback.snd q.val.hom (l ≫ k)))).app n
          (s, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p.val.hom q.val.hom (l ≫ k)).app n t))).val.app m α) x
  rw [Category.comp_id]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeCompComparison]
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_apply, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorPost_apply]
  have hc := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorComposition_apply a
    (Over.mk (pullback.snd p.val.hom (l ≫ k)))
    (Over.mk (pullback.snd q.val.hom (l ≫ k))) s
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPullback p.val.hom q.val.hom (l ≫ k)).app n t) α x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.iteratedPullbackInv_relativeFunctorPullback p.val.hom q.val.hom k l t α
    (s.val.app m α x)).symm.trans
      (congrArg ((pullbackLeftPullbackSndIso q.val.hom k l).inv.app m) hc).symm

/-- 概要：標準反復 pullback 比較は全添字・全対象の一つの共同図式比較。
方針：各添字の豊穣比較を、元の相対後合成と前合成の可換式で束ねる。
規約：成分の存在ではなく元の全比較を使う。使われ方：底変換合成の共同実現。 -/
def sectionBaseChangeCompComparison {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched (l ≫ k)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched l))) where
  component j := relativeBaseChangeCompEnrichedComparison k l (A.obj (Opposite.op j))
  naturality f p := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeFunctorPost_overPre (pullback.snd p.val.hom (l ≫ k))
    (pullback.snd (pullback.snd p.val.hom k) l) (pullbackLeftPullbackSndIso p.val.hom k l).inv
    (pullbackLeftPullbackSndIso_inv_snd_snd p.val.hom k l) (A.map f.op)

/-- 概要：共同図式比較を元の豊穣関手で前合成する。
方針：各成分の豊穣比較を前合成し添字の自然性を保つ。
規約：全高次 Hom を保持する。使われ方：二段の切断底変換の共通始域。 -/
def jointComparisonPrecompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison (D.precompose H) (E.precompose H) where
  component j := (η.component j).precompose H
  naturality f X := η.naturality f (H.obj X)

/-- 概要：共同図式の前合成は元の二つの豊穣関手の合成に一致する。
方針：対象と全高次 Hom の同じ定義を計算する。
規約：元の関手を保持する。使われ方：反復底変換の始域正規化。 -/
lemma jointDiagramPrecompose_assoc
    {C L M : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L] [Category.{u} M] [SimplicialCategory M]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram M J)
    (F : EnrichedFunctor SSet.{u} C L) (G : EnrichedFunctor SSet.{u} L M) :
    (D.precompose G).precompose F = D.precompose (F.comp SSet G) := by
  rfl

/-- 概要：共同図式比較は全添字・全対象での元の成分射で決まる。
方針：比較に記録された全高次自然性は命題なので成分の等式で消去する。
規約：ホモトピー圏の自然変換の点ごとの等式とは区別する。
使われ方：元の切断比較の合成を厳密な共同比較の等式へ束ねる。 -/
lemma jointComparison_ext
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η θ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E)
    (h : ∀ j p, (η.component j).val p = (θ.component j).val p) : η = θ := by
  cases η with
  | mk η hη =>
    cases θ with
    | mk θ hθ =>
      have he : η = θ := funext (fun j ↦ Subtype.ext (funext (fun p ↦ h j p)))
      subst θ
      rfl

/-- 概要：標準 pullback 比較と二回の元の底変換比較を合成する。
方針：全共同図式の豊穣比較を同じ始域へ制限して合成する。
規約：三つの元の比較を保持する。使われ方：一度の底変換比較との照合。 -/
def sectionBaseChangeComposite {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched (l ≫ k)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map (l ≫ k))) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans (sectionBaseChangeCompComparison k l A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans
      (jointComparisonPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison l A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison k (A ⋙ Over.map l)))

/-- 概要：二段の元の底変換比較の合成は一度の元の底変換比較と全共同図式で一致する。
方針：切断空間の元の合成則を全成分へ適用し、豊穣比較の等式へ束ねる。
規約：全高次自然性を持つ比較の等式。使われ方：指定実現同型の合成の入力。 -/
lemma sectionBaseChangeComposite_eq {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    sectionBaseChangeComposite k l A = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison (l ≫ k) A := by
  apply jointComparison_ext
  intro j p
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeForward_comp p.val.hom k l (A.obj (Opposite.op j)).hom

/-- 概要：共同標準 pullback 比較の各成分は元の厳密同型による同値。
方針：同じ切断空間の比較同型を使う。
規約：成分の射を選び直さない。使われ方：共同実現同型の可逆性入力。 -/
lemma sectionBaseChangeCompComparison_isQCatEquivalence {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T)
    (j : J) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched (l ≫ k))).obj j |>.obj p).obj)
      (Y := (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched l))).obj j
          |>.obj p).obj)
      (((sectionBaseChangeCompComparison k l A).component j).val p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeBaseChangeCompIso p.val.hom k l
    (A.obj (Opposite.op j)).hom)).isQCatEquivalence

/-- 概要：比較の前合成は各成分の同値性を保持する。
方針：元の比較を同じ豊穣関手の対象で評価する。
規約：全パラメーターを保持する。使われ方：二段底変換の共同実現の可逆性。 -/
lemma jointComparisonPrecompose_isQCatEquivalence
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p))
    (j : J) (p : L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := (((D.precompose H).obj j).obj p).obj)
      (Y := (((E.precompose H).obj j).obj p).obj)
      (((jointComparisonPrecompose η H).component j).val p) := hη j (H.obj p)

/-- 概要：共同比較の合成の各成分は、元の二つの同値の合成。
方針：元の各 Kan 空間の同値の合成則を使う。
規約：元の成分射を保持する。使われ方：共同合成の実現の可逆性入力。 -/
lemma jointComparisonTrans_isQCatEquivalence
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison E H)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p))
    (hθ : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((E.obj j).obj p).obj) (Y := ((H.obj j).obj p).obj) ((θ.component j).val p))
    (j : J) (p : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (X := ((D.obj j).obj p).obj) (Y := ((H.obj j).obj p).obj)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans η θ).component j).val p) := (hη j p).comp (hθ j p)

/-- 概要：同じ共同比較の表示変更は元の指定実現同型を変えない。
方針：比較の等式を消去し可逆性証明の命題性を使う。
規約：比較のデータの等式を要求する。使われ方：共同合成の指定実現同型の照合。 -/
lemma jointRealizationIso_congr
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    {η θ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E} (h : η = θ)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p))
    (hθ : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((θ.component j).val p)) :
    η.realizationIso hη = θ.realizationIso hθ := by
  cases h
  rfl

/-- 概要：標準 pullback 比較と二回の元の底変換を、三つの指定実現同型として合成する。
方針：全共同比較の既存 realizationIso を順に合成する。
規約：指定同型を選び直さない。使われ方：一度の指定実現同型との比較。 -/
def sectionBaseChangeCompositeRealizationIso {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram A).precompose
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched (l ≫ k))).realization)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionEnrichedDiagram (A ⋙ Over.map (l ≫ k))).realization) := by
  let η := sectionBaseChangeCompComparison k l A
  let θ := jointComparisonPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison l A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k)
  let ρ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison k (A ⋙ Over.map l)
  exact η.realizationIso (sectionBaseChangeCompComparison_isQCatEquivalence k l A) ≪≫
    θ.realizationIso (jointComparisonPrecompose_isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison l A) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison_isQCatEquivalence l A)) ≪≫
    ρ.realizationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison_isQCatEquivalence k (A ⋙ Over.map l))

/-- 概要：三つの指定実現同型の合成は一度の元の底変換比較の指定実現同型。
方針：共同三角形の合成則を二回適用し、元の共同比較の等式を使う。
規約：全図式の同型の等式。使われ方：P-12 の指定底変換合成則の降下前の入力。 -/
lemma sectionBaseChangeCompositeRealizationIso_eq {B D T : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (l : T ⟶ D) (A : Jᵒᵖ ⥤ Over T) :
    sectionBaseChangeCompositeRealizationIso k l A =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison (l ≫ k) A).realizationIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison_isQCatEquivalence (l ≫ k) A) := by
  let η := sectionBaseChangeCompComparison k l A
  let θ := jointComparisonPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison l A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k)
  let ρ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison k (A ⋙ Over.map l)
  let hη := sectionBaseChangeCompComparison_isQCatEquivalence k l A
  let hθ := jointComparisonPrecompose_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison l A) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationBaseChangeEnriched k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison_isQCatEquivalence l A)
  let hρ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeSectionBaseChangeComparison_isQCatEquivalence k (A ⋙ Over.map l)
  let hθρ := jointComparisonTrans_isQCatEquivalence θ ρ hθ hρ
  let hηθρ := jointComparisonTrans_isQCatEquivalence η (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans θ ρ) hη hθρ
  change η.realizationIso hη ≪≫ θ.realizationIso hθ ≪≫ ρ.realizationIso hρ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointRealizationIso_trans θ ρ hθ hρ hθρ,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointRealizationIso_trans η (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonTrans θ ρ) hη hθρ hηθρ]
  exact jointRealizationIso_congr (sectionBaseChangeComposite_eq k l A) _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
