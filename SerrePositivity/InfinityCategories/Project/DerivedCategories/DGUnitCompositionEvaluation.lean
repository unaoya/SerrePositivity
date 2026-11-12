module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUnitCompositionMap
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
/-!
概要：単位からの実射と全 Hom の自然性を、同じ厳密 dg 比較へ接続する。
方針：元の斉次合成と実分解の三成分の等式を使う。
規約：出力の射影性と入力の Small 性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R] {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
lemma dgUnitPostcomp_apply {x y z : E}
    (i : 𝟙_ (Complex R) ⟶ homObject R E y z)
    {k : ℤ} (f : GradedHom R x y k) :
    (((ρ_ (homObject R E x y)).inv ≫ _ ◁ i ≫ eComp (Complex R) x y z).f k) f =
      compose R (cycleFromUnit _ i).val f (add_zero k) := by
  simp only [compose, mul_zero, Int.negOnePow_zero, one_smul, forward]
  change (eComp (Complex R) x y z).f k
    ((_ ◁ i).f k ((ρ_ (homObject R E x y)).inv.f k f)) = _
  apply congrArg ((eComp (Complex R) x y z).f k)
  rw [complexRightUnitor_inv_apply]
  change ((ιTensorObj (homObject R E x y) (𝟙_ (Complex R)) k 0 k (add_zero k) ≫
      (homObject R E x y ◁ i).f k).hom
      (f ⊗ₜ[R] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R))) = _
  rw [ι_whiskerLeft]
  rfl
lemma dgUnitPrecomp_apply {x y z : E}
    (i : 𝟙_ (Complex R) ⟶ homObject R E x y)
    {k : ℤ} (f : GradedHom R y z k) :
    (((λ_ (homObject R E y z)).inv ≫ i ▷ _ ≫ eComp (Complex R) x y z).f k) f =
      compose R f (cycleFromUnit _ i).val (zero_add k) := by
  simp only [compose, zero_mul, Int.negOnePow_zero, one_smul, forward]
  change (eComp (Complex R) x y z).f k
    ((i ▷ _).f k ((λ_ (homObject R E y z)).inv.f k f)) = _
  apply congrArg ((eComp (Complex R) x y z).f k)
  rw [complexLeftUnitor_inv_apply]
  change ((ιTensorObj (𝟙_ (Complex R)) (homObject R E y z) 0 k k (zero_add k) ≫
      (i ▷ homObject R E y z).f k).hom
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R) ⊗ₜ[R] f)) = _
  rw [ι_whiskerRight]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
