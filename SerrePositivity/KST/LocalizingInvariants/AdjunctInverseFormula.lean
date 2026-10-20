module

public import SerrePositivity.InfinityCategories.F1B.AdjunctParameterNaturality
public import SerrePositivity.InfinityCategories.F1B.FunctorHomCorrespondence

/-!
概要：h Fun の逆 adjunct は左関手による後合成と余単位との合成である。
方針：双圏の逆 adjunct の公式を厳密な QCat の h Fun の表示へ移す。
規約：対象ごとの等式ではない。使われ方：差の単位の D 成分と cofiber 射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
local instance adjunctInverseHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

lemma adjunctInverseHomFormula {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (U : Z ⟶ X) (V : Z ⟶ Y) (α : FunctorHom U (V ≫ G)) :
    (a.homEquiv U V).symm α =
      (hoFunctor.map ((ihom Z).map F)).toFunctor.map α ≫
        (hoFunctor.map ((pre V).app Y)).toFunctor.map a.counitHom := by
  obtain ⟨γ, rfl⟩ := (qcatCellEquiv U (V ≫ G)).surjective α
  change qcatCellEquiv (U ≫ F) V ((a.homEquiv₂).symm γ) = _
  rw [Bicategory.Adjunction.homEquiv₂_symm_apply]
  simp only [Strict.associator_eqToIso, Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp]
  have hε := qcatCell_whiskerLeft V a.counit
  change qcatCellEquiv _ _ (qcatMap V ◁ a.counit) =
    (hoFunctor.map ((pre V).app Y)).toFunctor.map a.counitHom at hε
  exact ((qcatHomFunctor Z Y).map_comp (γ ▷ qcatMap F) (qcatMap V ◁ a.counit)).trans
    (congrArg₂ (fun f g => f ≫ g) (qcatCell_whiskerRight γ F) hε)

end SerrePositivity.KST.LocalizingInvariants
