module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ProductGraphFiber
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedNerveParameter
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveTransport

/-!
概要：同じ weighted 共同射影を添字のグラフへ戻すと、元の係数値そのものと底上で同型。
方針：元の添字 fiber の同型とグラフ fiber の同型を合成し、両射影の一致を保つ。
規約：全空間の同値だけでなく、元の係数包含と元の底への射影を厳密に回収する。
使われ方：section product scaffold の元の fiber 比較の同値性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 射影の等式で fiber を移しても元の全空間への包含は変わらない。 -/
lemma vertexFiber_eqToIso_ι {X B : SSet.{u}} {p q : X ⟶ B} (h : p = q) (b : B _⦋0⦌) :
    (eqToIso (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber t b) h)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  cases h
  exact Category.id_comp _

variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 元の定値係数の包含は、元の係数射影を保持する。 -/
lemma weightedNerveConstantLift_parameter (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η = η.app i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change SSet.yonedaEquiv
    ((SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ SSet.yonedaEquiv.symm x) ≫ η.app i) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id]
  change SSet.yonedaEquiv (((𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm x) ≫ η.app i) = _
  rw [Category.id_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じグラフの fiber 同型の逆は、元の全空間への包含を保持する。 -/
lemma productGraphFiberIso_inv_fst {E : SSet.{u}} (q : E ⟶ B ⊗ nerve I) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.productGraphFiberIso q i).inv ≫ pullback.fst q (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (q ≫ snd B (nerve I)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.productGraphFiberInverse q i ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.productGraphFiberInverse, pullback.lift_fst]

/-- 元の係数値と、同じ weighted 共同射影の添字グラフへの引き戻しとの同型。 -/
def weightedParameterGraphIso (i : I) : F.obj i ≅
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F i ≪≫
    eqToIso (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η ≫ snd B (nerve I) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F
        from lift_snd _ _).symm) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.productGraphFiberIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η) i).symm

/-- 同じグラフ同型の元の全空間への射は、元の定値包含そのもの。 -/
lemma weightedParameterGraphIso_fst (i : I) :
    (weightedParameterGraphIso η i).hom ≫ pullback.fst _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F i := by
  simp only [weightedParameterGraphIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    productGraphFiberIso_inv_fst]
  have h := vertexFiber_eqToIso_ι
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η ≫ snd B (nerve I)
      from (lift_snd _ _).symm) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
  exact (congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso F i).hom ≫ f) h).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberIso_hom_ι F i)

/-- 同じグラフ同型は、元の底への係数射影を厳密に保持する。 -/
lemma weightedParameterGraphIso_snd (i : I) :
    (weightedParameterGraphIso η i).hom ≫ pullback.snd _ _ = η.app i := by
  have hp : pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η = pullback.snd _ _ := by
    have h := congrArg (fun t ↦ t ≫ fst B (nerve I))
      (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η)
        (g := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase B i))
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.underSectionFiberBase,
      lift_fst, Category.comp_id] at h
    exact h
  rw [← hp, ← Category.assoc, weightedParameterGraphIso_fst, weightedNerveConstantLift_parameter]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
