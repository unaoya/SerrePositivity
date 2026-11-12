module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RelativeBaseChangeComposition

/-!
概要：底上の前合成は、相対関手空間の宇宙変更と全空間の同型による移送に自然である。
方針：宇宙変更は全内部 Hom の単体で計算し、同型の移送は前後合成の可換性で示す。
規約：底への等式を指定した Over の射を使い、表示の等式の証明に依存しない。
使われ方：G8 の四角形①の相対自然性を、元の小さい切断表示へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底上の前合成は、同じ底を保つ相対関手空間の宇宙持ち上げと可換。 -/
lemma uliftRelativeFunctorMap_overPre {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) :
    (SSet.uliftFunctor.{v, u}).map (relativeFunctorOverPre p f) ≫ uliftRelativeFunctorMap p a.hom =
      uliftRelativeFunctorMap p b.hom ≫ relativeFunctorOverPre ((SSet.uliftFunctor.{v, u}).map p)
        (show Over.mk ((SSet.uliftFunctor.{v, u}).map a.hom) ⟶
            Over.mk ((SSet.uliftFunctor.{v, u}).map b.hom) from
          Over.homMk ((SSet.uliftFunctor.{v, u}).map f.left) (by
            change (SSet.uliftFunctor.{v, u}).map f.left ≫
              (SSet.uliftFunctor.{v, u}).map b.hom = (SSet.uliftFunctor.{v, u}).map a.hom
            rw [← Functor.map_comp, f.w])) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 始域を同型で写してから前合成する四角形は、同じ標的の同型による移送と可換。 -/
lemma relativeFunctorOverIso_pre_hom {B : SSet.{u}} {a b b' p p' : Over B}
    (f : a ⟶ b) (eb : b ≅ b') (ep : p ≅ p') :
    relativeFunctorOverPre p.hom f ≫ (relativeFunctorOverIso (Iso.refl a) ep).hom =
      (relativeFunctorOverIso eb ep).hom ≫ relativeFunctorOverPre p'.hom (f ≫ eb.hom) := by
  rw [relativeFunctorOverIso_hom, relativeFunctorOverIso_hom]
  simp only [Iso.refl_inv, relativeFunctorOverPre_id, Category.id_comp]
  rw [Category.assoc,
    ← SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.relativeFunctorPost_overPre,
    ← Category.assoc,
    ← relativeFunctorOverPre_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
