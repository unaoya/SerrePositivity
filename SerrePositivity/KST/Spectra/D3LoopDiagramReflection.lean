module

public import SerrePositivity.KST.Spectra.D3LoopDiagramTranspose
public import SerrePositivity.KST.Spectra.D3StageLoopImageComparison

/-!
概要：実 loop 全図式の零角交換から、始点評価の coherent な自己同型を構成する。
方針：終点を固定した転置比較を持ち上げ、二回の転置と指定射影の充満忠実性を使う。
規約：転置比較の始点を恒等とは置かない。円の因子比較や安定性仮定は使わない。
使われ方：段比較へ保持すべき模型補正を、実図式の作用で扱うための界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 後合成で固定される評価を取ると、端点正規化前の同じ指定同型を回収する。 -/
lemma d3FunctorIsoOfEq_postcomp_fixed_heq {A B C : SSet.{u}}
    {f g f' g' : A ⟶ B} (e : FunctorIso f g) (t : B ⟶ B) (p : B ⟶ C)
    (hp : t ≫ p = p) (hf : f ≫ t = f') (hg : g ≫ t = g') :
    HEq ((F2.functorIsoOfEq (e.postcomp t) hf hg).postcomp p) (e.postcomp p) :=
  (functorIsoOfEq_postcomp_heq (e.postcomp t) hf hg p).trans
    ((heq_of_eq (F2.functorIso_postcomp_postcomp e t p)).trans
      (F2.functorIso_postcomp_heq_of_map_eq e hp).symm)

variable {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X]
  (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)

/-- 同じ終点を固定し、元の全図式をその零角交換へ比較する指定同型。 -/
def d3LoopDiagramTransposeIso :
    FunctorIso (𝟙 (loopDiagrams X)) (d3LoopDiagramTranspose X) :=
  loopDiagramFamilyIso_of_section s hs _ _ (by
    rw [Category.id_comp, d3LoopDiagramTranspose_corner])

lemma d3LoopDiagramTransposeIso_target_isEq :
    F2.IsFunctorEqIso ((d3LoopDiagramTransposeIso s hs).postcomp
      (loopDiagramEvaluation X 1 1)) := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  have ht : 𝟙 (loopDiagrams X) ≫ loopDiagramEvaluation X 1 1 =
      d3LoopDiagramTranspose X ≫ loopDiagramEvaluation X 1 1 := by
    rw [Category.id_comp, d3LoopDiagramTranspose_corner]
  exact d3IsFunctorEqIso_of_eqToIso _ ht
    (functorIsoOfTrivialKanFibration_postcomp _ _ _ ht)

/-- 同じ転置比較をもう一度転置し、二回転置の厳密等式で戻した指定値。 -/
def d3LoopDiagramTransposeReverseIso :
    FunctorIso (d3LoopDiagramTranspose X) (𝟙 (loopDiagrams X)) :=
  F2.functorIsoOfEq ((d3LoopDiagramTransposeIso s hs).postcomp (d3LoopDiagramTranspose X))
    (Category.id_comp _) (d3LoopDiagramTranspose_comp_self X)

private lemma d3LoopDiagramTransposeReverseIso_post_heq (i : Fin 2) :
    HEq ((d3LoopDiagramTransposeReverseIso s hs).postcomp (loopDiagramEvaluation X i i))
      ((d3LoopDiagramTransposeIso s hs).postcomp (loopDiagramEvaluation X i i)) := by
  exact d3FunctorIsoOfEq_postcomp_fixed_heq (d3LoopDiagramTransposeIso s hs)
    (d3LoopDiagramTranspose X) (loopDiagramEvaluation X i i)
    (d3LoopDiagramTranspose_corner X i i) (Category.id_comp _)
    (d3LoopDiagramTranspose_comp_self X)

/-- 転置比較と、同じ比較の転置から戻した値は、全図式上で互いに逆。 -/
lemma d3LoopDiagramTransposeIso_reverse :
    d3LoopDiagramTransposeIso s hs ≪≫ d3LoopDiagramTransposeReverseIso s hs = Iso.refl _ := by
  let := loopDiagramEvaluation_target_trivialKanFibration_of_section X s hs
  let hf := isFullyFaithful_of_trivialKanFibration (loopDiagramEvaluation X 1 1)
  apply hf.postcomp_functorIso_injective
  rw [F2.functorIso_postcomp_trans]
  have h0 := d3LoopDiagramTransposeIso_target_isEq s hs
  have h1 : F2.IsFunctorEqIso ((d3LoopDiagramTransposeReverseIso s hs).postcomp
      (loopDiagramEvaluation X 1 1)) := by
    apply h0.of_heq
      (by rw [Category.id_comp, d3LoopDiagramTranspose_corner])
      (by rw [Category.id_comp, d3LoopDiagramTranspose_corner])
    exact d3LoopDiagramTransposeReverseIso_post_heq s hs 1
  exact d3FunctorEqIso_unique (h0.trans h1) ((show F2.IsFunctorEqIso
    (show FunctorIso (𝟙 (loopDiagrams X)) (𝟙 (loopDiagrams X)) from Iso.refl _) from
      ⟨rfl, rfl⟩).postcomp (loopDiagramEvaluation X 1 1))

/-- 実 loop 全図式の零角交換が始点評価に誘導する、全関手自己同型。 -/
def d3LoopDiagramReflection :
    FunctorIso (loopDiagramEvaluation X 0 0) (loopDiagramEvaluation X 0 0) :=
  F2.functorIsoOfEq ((d3LoopDiagramTransposeIso s hs).postcomp (loopDiagramEvaluation X 0 0))
    (Category.id_comp _) (d3LoopDiagramTranspose_corner X 0 0)

private lemma d3FunctorIsoOfEq_refl {A Y : SSet.{u}} {f g : A ⟶ Y} (h : f = g) :
    F2.functorIsoOfEq (show FunctorIso f f from Iso.refl _) h h = Iso.refl _ := by
  subst g
  rfl

private lemma d3LoopDiagramTransposeReverseIso_source :
    F2.functorIsoOfEq
      ((d3LoopDiagramTransposeReverseIso s hs).postcomp (loopDiagramEvaluation X 0 0))
      (d3LoopDiagramTranspose_corner X 0 0) (Category.id_comp _) =
    d3LoopDiagramReflection s hs := by
  unfold d3LoopDiagramReflection
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    ((d3LoopDiagramTransposeReverseIso_post_heq s hs 0).trans
      (F2.functorIsoOfEq_heq _ _ _).symm))

/-- 二つの零角の反転は、全関手空間で二回の合成が恒等になる。 -/
lemma d3LoopDiagramReflection_involution :
    d3LoopDiagramReflection s hs ≪≫ d3LoopDiagramReflection s hs = Iso.refl _ := by
  let ev := loopDiagramEvaluation X 0 0
  have hrefl : (show FunctorIso (𝟙 (loopDiagrams X)) (𝟙 (loopDiagrams X)) from
      Iso.refl _).postcomp ev = Iso.refl _ := by
    rw [F2.functorIso_postcomp_eq_mapIso]
    exact Functor.mapIso_refl _ _
  have hp : (d3LoopDiagramTransposeIso s hs).postcomp ev ≪≫
      (d3LoopDiagramTransposeReverseIso s hs).postcomp ev =
        (show FunctorIso (𝟙 (loopDiagrams X) ≫ ev) (𝟙 (loopDiagrams X) ≫ ev) from
          Iso.refl _) ≪≫ Iso.refl _ := by
    rw [← F2.functorIso_postcomp_trans, d3LoopDiagramTransposeIso_reverse, hrefl]
    exact (Iso.refl_trans _).symm
  have ht := d3FunctorIso_square_transport _ _ _ _
    (Category.id_comp ev) (d3LoopDiagramTranspose_corner X 0 0)
    (Category.id_comp ev) (Category.id_comp ev) hp
  rw [d3LoopDiagramTransposeReverseIso_source, d3FunctorIsoOfEq_refl] at ht
  simpa only [d3LoopDiagramReflection, ev, Iso.refl_trans] using ht

/-- 反転の始点作用は、全図式の任意の指定同型と全関手空間で自然。 -/
lemma d3LoopDiagramReflection_naturality {A : SSet.{u}}
    {F G : A ⟶ loopDiagrams X} (e : FunctorIso F G) :
    e.postcomp (loopDiagramEvaluation X 0 0) ≪≫ (d3LoopDiagramReflection s hs).precomp G =
      (d3LoopDiagramReflection s hs).precomp F ≪≫ e.postcomp (loopDiagramEvaluation X 0 0) :=
  F2.functorIso_whisker_exchange e (d3LoopDiagramReflection s hs)

end SerrePositivity.KST.Spectra
