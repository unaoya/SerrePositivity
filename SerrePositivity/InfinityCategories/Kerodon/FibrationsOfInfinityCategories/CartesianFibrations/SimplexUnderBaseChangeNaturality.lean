module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexUnderBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeSectionInitialRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionBaseChange

/-!
概要：単体圏のunderを底変換し、同じ指定定義域写像と自然変換を比較する。
方針：Under.postの式で自然変換を定め、始対象の点包含によって切断制限の同値性を検出する。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の法則。
  射を存在命題から選ばず、全添字で自然な同じ変換を保持する。
使われ方：S8のP3-B2a〜d、共同切断の指定合成則への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
noncomputable section

/-- underの指定定義域写像はUnder.postによる底変換と厳密に両立する。 -/
@[cite HTT "3.3.2" (partial := special) "単体圏underの指定底変換の照合法則。"]
lemma transportSimplexUnderDomainMap_baseChange {B D : SSet.{u}} (k : D ⟶ B)
    (s : TransportSimplexCategory D) :
    nerveMap (Under.post (X := s) (transportSimplexFunctor k)) ≫
      transportSimplexUnderDomainMap ((transportSimplexFunctor k).obj s) =
    transportSimplexUnderDomainMap s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro τ
  apply stdSimplex.ext
  intro i
  rfl

/-- Under.postそのものを成分に持つ、元の底上での自然変換。 -/
@[cite HTT "3.3.2" (partial := special) "単体圏underの指定底変換の照合法則。"]
def transportSimplexUnderBaseChangeTransformation {B D : SSet.{u}} (k : D ⟶ B) :
    transportSimplexUnderDomains D ⋙ Over.map k ⟶
      (transportSimplexFunctor k).op ⋙ transportSimplexUnderDomains B where
  app s := Over.homMk (nerveMap (Under.post (X := s.unop) (transportSimplexFunctor k))) (by
    let H := transportSimplexFunctor k
    have h₁ : nerveMap (Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop)) =
        nerveMap (Under.post (X := s.unop) H) ≫ nerveMap (Under.forget (H.obj s.unop)) :=
      nerveFunctor.map_comp (Under.post (X := s.unop) H).toCatHom
        (Under.forget (H.obj s.unop)).toCatHom
    have h₂ : nerveMap (Under.forget s.unop ⋙ H) =
        nerveMap (Under.forget s.unop) ≫ nerveMap H :=
      nerveFunctor.map_comp (Under.forget s.unop).toCatHom H.toCatHom
    have hF : Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop) =
        Under.forget s.unop ⋙ H := rfl
    change nerveMap (Under.post (X := s.unop) H) ≫
        (nerveMap (Under.forget (H.obj s.unop)) ≫ transportSimplexFirstVertexMap B) =
      (nerveMap (Under.forget s.unop) ≫ transportSimplexFirstVertexMap D) ≫ k
    rw [← Category.assoc, ← h₁, hF, h₂, Category.assoc,
      transportSimplexFirstVertexMap_naturality k, ← Category.assoc])
  naturality {s t} f := by
    apply Over.OverMorphism.ext
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      change Under.mk ((transportSimplexFunctor k).map (f.unop ≫ (τ.obj i).hom)) =
        Under.mk ((transportSimplexFunctor k).map f.unop ≫
          (transportSimplexFunctor k).map (τ.obj i).hom)
      rw [Functor.map_comp]
    case h_map =>
      intro i j g
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      apply StructuredArrow.hom_ext
      rfl

/-- 指定した二つの定義域への自然変換を、同じUnder.postの変換が仲介する。 -/
@[cite HTT "3.3.2" (partial := special) "単体圏underの指定底変換の照合法則。"]
lemma transportSimplexUnderTransformation_baseChange {B D : SSet.{u}} (k : D ⟶ B) :
    Functor.whiskerRight (transportSimplexUnderDomainTransformation D) (Over.map k) =
      transportSimplexUnderBaseChangeTransformation k ≫
        Functor.whiskerLeft (transportSimplexFunctor k).op
          (transportSimplexUnderDomainTransformation B) ≫
          eqToHom (transportSimplexDomainFunctor_baseChange k) := by
  apply NatTrans.ext
  funext s
  apply Over.OverMorphism.ext
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    eqToHom_app, Over.comp_left, Over.eqToHom_left]
  change transportSimplexUnderDomainMap s.unop =
    nerveMap (Under.post (X := s.unop) (transportSimplexFunctor k)) ≫
      transportSimplexUnderDomainMap ((transportSimplexFunctor k).obj s.unop) ≫ eqToHom _
  rw [eqToHom_refl, Category.comp_id]
  exact (transportSimplexUnderDomainMap_baseChange k s.unop).symm

/-- 始点を保つUnder.postへの切断制限は、任意のleft fibrationで同値。 -/
@[cite HTT "3.3.2" (partial := special) "単体圏underの指定底変換の照合法則。"]
lemma transportSimplexUnderBaseChangeComparison_isQCatEquivalence
    {B D : SSet.{u}} (k : D ⟶ B) (s : TransportSimplexCategory D)
    (p : LeftFibrationObject B) :
    IsQCatEquivalence (relativeFunctorOverPre p.val.hom
      ((transportSimplexUnderBaseChangeTransformation k).app (Opposite.op s))) := by
  let H := transportSimplexFunctor k
  let a := (transportSimplexUnderDomains D ⋙ Over.map k).obj (Opposite.op s)
  let b := ((transportSimplexFunctor k).op ⋙ transportSimplexUnderDomains B).obj
    (Opposite.op s)
  let f : a ⟶ b := (transportSimplexUnderBaseChangeTransformation k).app (Opposite.op s)
  let z := nervePoint (Under.mk (𝟙 s))
  let c := Over.mk (z ≫ a.hom)
  let r : c ⟶ a := Over.homMk z rfl
  let t : c ⟶ b := r ≫ f
  have hz : t.left = nervePoint (Under.mk (𝟙 (H.obj s))) := by
    change nervePoint (Under.mk (𝟙 s)) ≫
      nerveMap (Under.post (X := s) H) = nervePoint (Under.mk (𝟙 (H.obj s)))
    rw [nervePoint, nervePoint, SSet.yonedaEquiv_symm_comp]
    congr 1
  exact relativeFunctorOverPre_isQCatEquivalence_of_initialComparison p.val.hom f r t
    (nervePoint_leftAnodyne Under.mkIdInitial)
    (by rw [hz]; exact nervePoint_leftAnodyne Under.mkIdInitial) rfl
end
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
