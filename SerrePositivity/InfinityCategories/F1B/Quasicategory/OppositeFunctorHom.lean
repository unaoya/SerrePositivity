module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：関手の二胞体の反転と、恒等・標的での後合成との両立。
方針：既存の反転 Hom 全単射の合成則と、指定ホモトピー代表を使う。
規約：可逆でない二胞体も扱う。使われ方：K-8 の随伴の双対化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.F1B.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

lemma oppositeFunctorHom_id {A D : SSet.{u}} [Quasicategory D] (F : A ⟶ D) :
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F (𝟙 (HomotopyCategory.mk (functorVertex F))) = 𝟙 _ := by
  obtain ⟨α, hα⟩ := (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F F).surjective (𝟙 _)
  have h := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp (𝟙 (HomotopyCategory.mk (functorVertex F))) α
  rw [Category.id_comp, hα, Category.id_comp] at h
  exact h.symm

lemma oppositeFunctorHom_postcomp {A D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (p : D ⟶ E) {F G : A ⟶ D} (α : FunctorHom F G) :
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv (F ≫ p) (G ≫ p)
        ((hoFunctor.map ((ihom A).map p)).toFunctor.map α) =
      (hoFunctor.map ((ihom A.op).map (SSet.opFunctor.map p))).toFunctor.map
        (SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F G α) := by
  have h := functorHomHomotopy_hom α
  rw [← h, ← functorHomotopyPostcomp_hom, SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_homotopy,
    SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_homotopy, ← functorHomotopyPostcomp_hom]
  congr 1

end SerrePositivity.InfinityCategories.F1B.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeFunctorHom_id := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeFunctorHom_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.oppositeFunctorHom_postcomp := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.oppositeFunctorHom_postcomp
