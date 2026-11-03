module
public import SerrePositivity.KST.SConstruction.SerreIntervalTensorExt
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-! # 元の鎖区間の三重 tensor の生成元判定
概要：二端点と辺の全ての三つ組で、三重 tensor からの chain map を判定する。
方針：三重斉次成分を線形転置し、元の各次数の生成元判定を三回適用する。
規約：元の生成元と結合の順序を保つ。使われ方：max connection の結合則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の各次数の生成元で、任意の加群への線形写像を判定する。 -/
lemma serreInterval_degree_linear_ext (n : ℤ) {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (serreInterval A).X n →ₗ[A] M}
    (h : ∀ (i : Fin 3) (hi : serreIntervalGeneratorDegree i = n),
      f (eqToHom (congrArg (fun k => (serreInterval A).X k) hi) (serreIntervalGenerator A i)) =
      g (eqToHom (congrArg (fun k => (serreInterval A).X k) hi) (serreIntervalGenerator A i))) :
    f = g :=
  congrArg ModuleCat.Hom.hom
    (serreInterval_degree_hom_ext A n (f := ModuleCat.ofHom f) (g := ModuleCat.ofHom g) h)

/-- 元の区間の全生成元の三つ組で一致する三重 tensor chain map は等しい。 -/
lemma serreIntervalTriple_hom_ext {K : Complex A}
    {f g : (serreInterval A ⊗ serreInterval A) ⊗ serreInterval A ⟶ K}
    (h : ∀ (i j k : Fin 3) (n : ℤ)
      (hn : serreIntervalGeneratorDegree i + serreIntervalGeneratorDegree j +
        serreIntervalGeneratorDegree k = n),
      f.f n (ιTensorObj (serreInterval A ⊗ serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree i + serreIntervalGeneratorDegree j)
        (serreIntervalGeneratorDegree k) n hn
          (ιTensorObj (serreInterval A) (serreInterval A)
            (serreIntervalGeneratorDegree i) (serreIntervalGeneratorDegree j) _ rfl
              (serreIntervalGenerator A i ⊗ₜ[A] serreIntervalGenerator A j) ⊗ₜ[A]
            serreIntervalGenerator A k)) =
      g.f n (ιTensorObj (serreInterval A ⊗ serreInterval A) (serreInterval A)
        (serreIntervalGeneratorDegree i + serreIntervalGeneratorDegree j)
        (serreIntervalGeneratorDegree k) n hn
          (ιTensorObj (serreInterval A) (serreInterval A)
            (serreIntervalGeneratorDegree i) (serreIntervalGeneratorDegree j) _ rfl
              (serreIntervalGenerator A i ⊗ₜ[A] serreIntervalGenerator A j) ⊗ₜ[A]
            serreIntervalGenerator A k))) : f = g := by
  apply triple_ext
  intro p q r n hn
  let L := (ιTensorObj (serreInterval A) (serreInterval A) p q (p + q) rfl ▷
    (serreInterval A).X r) ≫
      ιTensorObj (serreInterval A ⊗ serreInterval A) (serreInterval A) (p + q) r n hn ≫ f.f n
  let R := (ιTensorObj (serreInterval A) (serreInterval A) p q (p + q) rfl ▷
    (serreInterval A).X r) ≫
      ιTensorObj (serreInterval A ⊗ serreInterval A) (serreInterval A) (p + q) r n hn ≫ g.f n
  apply ModuleCat.hom_ext
  change L.hom = R.hom
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply serreInterval_degree_linear_ext A p
  intro i hi
  rcases hi with rfl
  apply serreInterval_degree_linear_ext A q
  intro j hj
  rcases hj with rfl
  apply serreInterval_degree_linear_ext A r
  intro k hk
  rcases hk with rfl
  exact h i j k n hn

end SerrePositivity.KST.SConstruction
