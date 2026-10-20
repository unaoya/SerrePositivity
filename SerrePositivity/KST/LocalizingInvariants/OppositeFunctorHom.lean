module

public import SerrePositivity.InfinityCategories.F1B.KanFunctorOppositeHom
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants

lemma oppositeFunctorHom_id {A D : SSet.{u}} [Quasicategory D] (F : A ⟶ D) :
    kanFunctorOppositeHomEquiv F F (𝟙 (HomotopyCategory.mk (functorVertex F))) = 𝟙 _ := by
  obtain ⟨α, hα⟩ := (kanFunctorOppositeHomEquiv F F).surjective (𝟙 _)
  have h := kanFunctorOppositeHomEquiv_comp (𝟙 (HomotopyCategory.mk (functorVertex F))) α
  rw [Category.id_comp, hα, Category.id_comp] at h
  exact h.symm

lemma oppositeFunctorHom_postcomp {A D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (p : D ⟶ E) {F G : A ⟶ D} (α : FunctorHom F G) :
    kanFunctorOppositeHomEquiv (F ≫ p) (G ≫ p)
        ((hoFunctor.map ((ihom A).map p)).toFunctor.map α) =
      (hoFunctor.map ((ihom A.op).map (SSet.opFunctor.map p))).toFunctor.map
        (kanFunctorOppositeHomEquiv F G α) := by
  have h := functorHomHomotopy_hom α
  rw [← h, ← functorHomotopyPostcomp_hom, kanFunctorOppositeHomEquiv_homotopy,
    kanFunctorOppositeHomEquiv_homotopy, ← functorHomotopyPostcomp_hom]
  congr 1

end SerrePositivity.KST.LocalizingInvariants
