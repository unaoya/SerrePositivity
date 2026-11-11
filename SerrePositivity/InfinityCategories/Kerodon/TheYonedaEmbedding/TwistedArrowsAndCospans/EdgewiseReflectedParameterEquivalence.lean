module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseReflectedHomParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection

/-!
概要：反転した共通パラメーターへの制限から、元の Hom 全体の関手同型を回収する。
方針：左端の同値を反転・宇宙持ち上げで移し、その同じパラメーター逆で比較を戻す。
規約：追加パラメーターを固定せず、任意の単体集合のまま保持する。
使われ方：任意の coherent 変換を含む自然性四角形の比較を元の Hom へ降ろす。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- Kan な Hom の共通解像の反転した左端パラメーター射は同値。 -/
lemma edgewiseReflectedParameter_isQCatEquivalence (H : SSet.{u}) [KanComplex H] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H) := by
  have h₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft H)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeKanHomotopyEquivalence h₀.isSimplicialHomotopyEquivalence
  let d : H.op.op ≅ H := SSet.opFunctorCompOpFunctorIso.app H
  have h₂ := h₁.isQCatEquivalence.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso d).isQCatEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision H)).symm).isQCatEquivalence.comp
      h₂.ulift_of_kan

/-- 共通パラメーターへ制限した一つの関手同型を、元の Hom 全体へ戻す。 -/
def edgewiseReflectedParameter_descendIso (H : SSet.{u}) [KanComplex H]
    {K : SSet.{u + 1}} [Quasicategory K]
    {f g : (SSet.uliftFunctor.{u + 1, u}).obj H ⟶ K}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H ≫ g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  let e := (edgewiseReflectedParameter_isQCatEquivalence H).choose
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso.symm f ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp h e.inv ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso g

/-- 任意の追加パラメーター全体を保ったまま、同じ制限上の比較を元の Hom へ戻す。 -/
def edgewiseReflectedParameter_tensorDescendIso (H : SSet.{u}) [KanComplex H]
    {R K : SSet.{u + 1}} [KanComplex K]
    {f g : (SSet.uliftFunctor.{u + 1, u}).obj H ⊗ R ⟶ K}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H ▷ R) ≫ f)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H ▷ R) ≫ g)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  let M := (SSet.uliftFunctor.{u + 1, u}).obj H
  let e := (edgewiseReflectedParameter_isQCatEquivalence H).choose
  let V := e.invHomIso.simplicialHomotopy
  let W (k : M ⊗ R ⟶ K) :
      SSet.Homotopy ((e.inv ▷ R) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseReflectedParameter H ▷ R) ≫ k) k :=
    { h := lift
        (lift (fst (M ⊗ R) (Δ[1] : SSet.{u + 1}) ≫ fst M R)
          (snd (M ⊗ R) (Δ[1] : SSet.{u + 1})) ≫ V.h)
        (fst (M ⊗ R) (Δ[1] : SSet.{u + 1}) ≫ snd M R) ≫ k
      h₀ := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        rintro ⟨x, r⟩
        exact congrArg (fun z ↦ k.app n (z, r)) (congrArg (fun a ↦ a.app n x) V.h₀)
      h₁ := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        rintro ⟨x, r⟩
        exact congrArg (fun z ↦ k.app n (z, r)) (congrArg (fun a ↦ a.app n x) V.h₁)
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (W f)).symm ≪≫
    h.precomp (e.inv ▷ R) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (W g)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
