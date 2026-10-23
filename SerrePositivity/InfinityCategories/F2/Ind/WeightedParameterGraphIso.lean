module

public import SerrePositivity.InfinityCategories.F2.Ind.ProductGraphFiber
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedNerveParameter
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveTransport

/-!
概要：同じ weighted 共同射影を添字のグラフへ戻すと、元の係数値そのものと底上で同型。
方針：元の添字 fiber の同型とグラフ fiber の同型を合成し、両射影の一致を保つ。
規約：全空間の同値だけでなく、元の係数包含と元の底への射影を厳密に回収する。
使われ方：section product scaffold の元の fiber 比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 射影の等式で fiber を移しても元の全空間への包含は変わらない。 -/
lemma vertexFiber_eqToIso_ι {X B : SSet.{u}} {p q : X ⟶ B} (h : p = q) (b : B _⦋0⦌) :
    (eqToIso (congrArg (fun t ↦ vertexFiber t b) h)).hom ≫ vertexFiberι q b =
      vertexFiberι p b := by
  cases h
  exact Category.id_comp _

variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 元の定値係数の包含は、元の係数射影を保持する。 -/
lemma weightedNerveConstantLift_parameter (i : I) :
    weightedNerveConstantLift F i ≫ weightedNerveParameter η = η.app i := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  change SSet.yonedaEquiv
    ((SSet.stdSimplex.map (simplexPrefixInclusion n n _) ≫ SSet.yonedaEquiv.symm x) ≫ η.app i) = _
  rw [simplexPrefixInclusion_id]
  change SSet.yonedaEquiv (((𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm x) ≫ η.app i) = _
  rw [Category.id_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 同じグラフの fiber 同型の逆は、元の全空間への包含を保持する。 -/
lemma productGraphFiberIso_inv_fst {E : SSet.{u}} (q : E ⟶ B ⊗ nerve I) (i : I) :
    (productGraphFiberIso q i).inv ≫ pullback.fst q (underSectionFiberBase B i) =
      vertexFiberι (q ≫ snd B (nerve I)) (nerveVertex i) := by
  change productGraphFiberInverse q i ≫ pullback.fst _ _ = _
  rw [productGraphFiberInverse, pullback.lift_fst]

/-- 元の係数値と、同じ weighted 共同射影の添字グラフへの引き戻しとの同型。 -/
def weightedParameterGraphIso (i : I) : F.obj i ≅
    pullback (weightedNerveParameterProjection η) (underSectionFiberBase B i) :=
  weightedNerveFiberIso F i ≪≫
    eqToIso (congrArg (fun t ↦ vertexFiber t (nerveVertex i))
      (show weightedNerveParameterProjection η ≫ snd B (nerve I) = weightedNerveProjection F
        from lift_snd _ _).symm) ≪≫
    (productGraphFiberIso (weightedNerveParameterProjection η) i).symm

/-- 同じグラフ同型の元の全空間への射は、元の定値包含そのもの。 -/
lemma weightedParameterGraphIso_fst (i : I) :
    (weightedParameterGraphIso η i).hom ≫ pullback.fst _ _ = weightedNerveConstantLift F i := by
  simp only [weightedParameterGraphIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    productGraphFiberIso_inv_fst]
  have h := vertexFiber_eqToIso_ι
    (show weightedNerveProjection F = weightedNerveParameterProjection η ≫ snd B (nerve I)
      from (lift_snd _ _).symm) (nerveVertex i)
  exact (congrArg (fun f ↦ (weightedNerveFiberIso F i).hom ≫ f) h).trans
    (weightedNerveFiberIso_hom_ι F i)

/-- 同じグラフ同型は、元の底への係数射影を厳密に保持する。 -/
lemma weightedParameterGraphIso_snd (i : I) :
    (weightedParameterGraphIso η i).hom ≫ pullback.snd _ _ = η.app i := by
  have hp : pullback.fst (weightedNerveParameterProjection η) (underSectionFiberBase B i) ≫
      weightedNerveParameter η = pullback.snd _ _ := by
    have h := congrArg (fun t ↦ t ≫ fst B (nerve I))
      (pullback.condition (f := weightedNerveParameterProjection η)
        (g := underSectionFiberBase B i))
    simp only [Category.assoc, weightedNerveParameterProjection, underSectionFiberBase,
      lift_fst, Category.comp_id] at h
    exact h
  rw [← hp, ← Category.assoc, weightedParameterGraphIso_fst, weightedNerveConstantLift_parameter]

end SerrePositivity.InfinityCategories.F2.Ind
