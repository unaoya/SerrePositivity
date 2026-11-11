module
public import SerrePositivity.KST.SConstruction.SExactEnrichedFunctor

/-! # 元の全パラメータ自然性を保つ S_n 作用
概要：完全関手族の全単体に関する自然性四角形を、同じ元の S_n 作用へ移す。
方針：全 gapped 図式への包含後に各 Ar 成分で元の自然性を評価する。
規約：全入力パラメータを保持する。使われ方：有限反復の全多単体方向の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

private lemma family_evaluation {X Y P : SSet.{u}} (a : P ⟶ (ihom X).obj Y)
    {k m : SimplexCategoryᵒᵖ} (α : k ⟶ m) (p : P.obj k) (x : X.obj m) :
    (a.app k p).app m α x = (uncurry a).app m (x, P.map α p) := by
  have h := congrArg (fun z => z p) (a.naturality α).symm
  change ((ihom X).obj Y).map α (a.app k p) = a.app m (P.map α p) at h
  have hh := congrArg (fun z => z.app m (𝟙 m) x) h
  change (a.app k p).app m (α ≫ 𝟙 m) x = _ at hh
  rw [Category.comp_id] at hh
  exact hh

private lemma uncurry_parameter_action {X Y P Q : SSet.{u}}
    (a : P ⟶ Q) (b : X ⊗ Q ⟶ Y) :
    uncurry (a ≫ curry b) = (𝟙 X ⊗ₘ a) ≫ b := by
  rw [uncurry_natural_left, uncurry_curry, id_tensorHom]

private lemma internalComp_evaluation {X Y Z : SSet.{u}}
    {k m : SimplexCategoryᵒᵖ} (α : k ⟶ m)
    (a : ((ihom X).obj Y).obj k) (b : ((ihom Y).obj Z).obj k) (x : X.obj m) :
    ((MonoidalClosed.comp X Y Z).app k (a, b)).app m α x =
      b.app m α (a.app m α x) := by
  change b.app m (α ≫ 𝟙 m) (a.app m (α ≫ 𝟙 m) x) = _
  rw [Category.comp_id]

private lemma internalMap_evaluation {X Y Z : SSet.{u}} (f : Y ⟶ Z)
    {k m : SimplexCategoryᵒᵖ} (α : k ⟶ m) (a : ((ihom X).obj Y).obj k)
    (x : X.obj m) :
    (((ihom X).map f).app k a).app m α x = f.app m (a.app m α x) := by
  rfl

/-- 全パラメータに自然な完全関手族の四角形は、元の S_n の全作用でも自然。 -/
lemma sExactParameterizedNaturality (n : ℕ) {C D C' D' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {P : SSet.{u}} (a : P ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{u}))
    (b : P ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C' D' : SSet.{u})) (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C C') (g : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D D')
    (h : (f.hom ▷ P) ≫ uncurry (b ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C' D').ι) =
      uncurry (a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι) ≫ g.hom) :
    ((sExactMap n f).hom ▷ P) ≫ uncurry (b ≫ sExactFamilyMap n C' D') =
      uncurry (a ≫ sExactFamilyMap n C D) ≫ (sExactMap n g).hom := by
  change (sPostcompCofiber n f.hom
    (preservesCofiberData_of_isExactFunctor f.hom) ▷ P) ≫
      uncurry (b ≫ curry (sExactFamilyAction n C' D')) =
    uncurry (a ≫ curry (sExactFamilyAction n C D)) ≫ sPostcompCofiber n g.hom
      (preservesCofiberData_of_isExactFunctor g.hom)
  rw [uncurry_parameter_action, uncurry_parameter_action]
  ext k p
  apply Subtype.ext
  apply Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro q
  have hb := family_evaluation (b ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C' D').ι) α p.2
    (f.hom.app m (p.1.val.app m α q))
  have ha := family_evaluation (a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι) α p.2
    (p.1.val.app m α q)
  have hh := congrArg (fun z => z.app m (p.1.val.app m α q, P.map α p.2)) h
  change ((MonoidalClosed.comp (arNerve n) C'.obj D'.obj).app k
    (((ihom (arNerve n)).map f.hom).app k p.1.val, (b.app k p.2).val)).app m α q =
      g.hom.app m (((MonoidalClosed.comp (arNerve n) C.obj D.obj).app k
        (p.1.val, (a.app k p.2).val)).app m α q)
  erw [internalComp_evaluation, internalComp_evaluation]
  erw [internalMap_evaluation]
  exact hb.trans (hh.trans (congrArg (fun x => g.hom.app m x) ha.symm))

end SerrePositivity.KST.SConstruction
