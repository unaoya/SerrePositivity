module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FamilyCurryCoherence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation

/-!
概要：族の currying と指定頂点での評価の整合性。
方針：内部 currying の後の評価を元の積の底上の前合成と同定する。
規約：全ての高次単体での射の等式から同型の評価を得る。
使われ方：普遍余単位の実際の成分を選択した分類と接続する。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：内部 currying の後の頂点評価は積の底上のその頂点への制限。
方針：評価の単位による表示と curry・uncurry の往復を使う。
規約：充填性や小ささの仮定は不要。
使われ方：族の比較を各成分の比較へ移す。 -/
lemma coherentFamilyCurryMap_evaluate (A X : SSet.{u}) {K : SSet.{u}} (k : K _⦋0⦌) :
    (ihomCurryIso A K X).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj X) k =
      (pre (lift (𝟙 A) (SSet.const k))).app X := by
  let Q := (ihom (A ⊗ K)).obj X
  let v := (SSet.unitHomEquiv K).symm k
  have hv : SSet.unitHomEquiv K v = k := (SSet.unitHomEquiv K).apply_symm_apply k
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv
    (curry ((α_ A K Q).inv ≫ (ihom.ev (A ⊗ K)).app X)) v
  rw [hv] at he
  change curry (curry ((α_ A K Q).inv ≫ (ihom.ev (A ⊗ K)).app X)) ≫ _ = _
  rw [he]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry]
  have hu := uncurry_pre (lift (𝟙 A) (SSet.const k) : A ⟶ A ⊗ K) X
  rw [hu]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hp : (A ◁ ((λ_ Q).inv ≫ (v ▷ Q))) ≫ (α_ A K Q).inv =
      lift (𝟙 A) (SSet.const k) ▷ Q := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [← Category.assoc, hp]

/-- 概要：curry した図式の頂点評価は元の図式のその頂点への制限を回収する。
方針：内部 currying の評価の射の等式を関手頂点で評価する。
規約：端点の厳密な等式。
使われ方：族の同型の評価で両端を同定する。 -/
lemma coherentFamilyCurryMap_evaluate_vertex {A K X : SSet.{u}}
    (f : A ⊗ K ⟶ X) (k : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj X) k).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (𝟙 A) (SSet.const k) ≫ f) :=
  congrArg (fun h ↦ h.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (coherentFamilyCurryMap_evaluate A X k)

/-- 概要：curry した同型の頂点評価は元の同型のその頂点への制限。
方針：内部 currying と評価の可換式を同型の像へ写す。
規約：始点と終点の評価の等式で同じ比較を移送する。
使われ方：普遍余単位の成分の比較の主要式。 -/
lemma coherentFamilyCurryIso_evaluate {A K X : SSet.{u}} {f g : A ⊗ K ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (k : K _⦋0⦌) :
    (eqToIso (congrArg SSet.HomotopyCategory.mk
      (coherentFamilyCurryMap_evaluate_vertex f k))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentFamilyCurryIso e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj X) k) ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (coherentFamilyCurryMap_evaluate_vertex g k)) =
      e.precomp (lift (𝟙 A) (SSet.const k)) := by
  change (eqToIso _).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (ihomCurryIso A K X).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom A).obj X) k) ≪≫ eqToIso _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e ((pre (lift (𝟙 A) (SSet.const k))).app X)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_congr e _ _ (coherentFamilyCurryMap_evaluate A X k)]
  apply Iso.ext
  simp

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
