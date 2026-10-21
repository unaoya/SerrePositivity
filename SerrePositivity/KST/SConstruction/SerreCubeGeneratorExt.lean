module
public import SerrePositivity.KST.SConstruction.SerreCubeGenerators

/-! # 元の全 Serre cube の生成元による射の判定
概要：元の全端点・辺 tensor 生成元の値で、各次数の線形射と全鎖射を判定する。
方針：元の区間の次数判定、tensor の双次数包含、線形転置を次元に関して帰納する。
規約：元の非有界 tensor の全次数を保持。使われ方：逆構成の全生成元回収と一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全端点・辺 tensor 生成元の指定次数での値から、元の次数線形射の等号を判定。 -/
lemma serreCube_degree_hom_ext (n : ℕ) (k : ℤ) {V : ModuleCat.{u} A}
    {f g : (serreCubeComplex A n).X k ⟶ V}
    (h : ∀ (i : SerreCubeGeneratorIndex n) (hi : serreCubeGeneratorDegree n i = k),
      f (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
        (serreCubeGenerator A n i)) =
      g (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hi)
        (serreCubeGenerator A n i))) : f = g := by
  induction n generalizing k V with
  | zero =>
    by_cases hk : k = 0
    · subst k
      apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv).1
      apply (moduleElementEquiv A V).injective
      exact h PUnit.unit rfl
    · exact (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) k hk).eq_of_src _ _
  | succ n ih =>
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    let L := ιTensorObj (serreCubeComplex A n) (serreInterval A) p q k hpq ≫ f
    let R := ιTensorObj (serreCubeComplex A n) (serreInterval A) p q k hpq ≫ g
    apply ModuleCat.hom_ext
    change L.hom = R.hom
    apply TensorProduct.curry_injective
    have hc : (ModuleCat.ofHom (TensorProduct.curry L.hom) : (serreCubeComplex A n).X p ⟶
        ModuleCat.of A ((serreInterval A).X q →ₗ[A] V)) =
        ModuleCat.ofHom (TensorProduct.curry R.hom) := by
      apply ih
      intro i hi
      subst p
      have hd : (ModuleCat.ofHom ((TensorProduct.curry L.hom) (serreCubeGenerator A n i)) :
          (serreInterval A).X q ⟶ V) =
          ModuleCat.ofHom ((TensorProduct.curry R.hom) (serreCubeGenerator A n i)) := by
        apply serreInterval_degree_hom_ext A q
        intro j hj
        subst q
        have he := serreCubeGenerator_succ_cast A n i j k hpq
        exact (congrArg (fun w => f w) he).symm.trans
          ((h (i, j) hpq).trans (congrArg (fun w => g w) he))
      exact congrArg ModuleCat.Hom.hom hd
    exact congrArg ModuleCat.Hom.hom hc

/-- 元の全端点・辺 tensor 生成元で一致する元の鎖射は等しい。 -/
lemma serreCube_generator_hom_ext (n : ℕ) {K : Complex A}
    {f g : serreCubeComplex A n ⟶ K}
    (h : ∀ i : SerreCubeGeneratorIndex n,
      f.f (serreCubeGeneratorDegree n i) (serreCubeGenerator A n i) =
        g.f (serreCubeGeneratorDegree n i) (serreCubeGenerator A n i)) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply serreCube_degree_hom_ext A n k
  intro i hi
  rcases hi with rfl
  exact h i

end SerrePositivity.KST.SConstruction
