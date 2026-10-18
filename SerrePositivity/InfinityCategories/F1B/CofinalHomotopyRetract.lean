module

public import SerrePositivity.InfinityCategories.F1B.CofinalFunctorPreHomotopy
public import SerrePositivity.InfinityCategories.F1B.CofinalSectionHomotopy

/-!
概要：底上の切断と収縮から左右 cofinality を得る。
方針：切断による制限を逆とし、一方の合成は厳密に、他方は底上のホモトピーで戻す。
規約：元の二対象に Kan 性や quasicategory 性を課さない。
使われ方：任意の trivial Kan fibration の左右 cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上の収縮を持つ射に沿う相対関手の制限はホモトピー同値。
方針：切断による前合成を逆にし、底上の射の合成則とホモトピー作用を使う。
規約：検査対象 p にも fibration 性を要求しない。
使われ方：左右 cofinality に共通する十分条件。 -/
lemma CofinalSectionHomotopy.restriction_isSimplicialHomotopyEquivalence
    {A B E : SSet.{u}} {f : A ⟶ B} (d : CofinalSectionHomotopy f) (p : E ⟶ B) :
    IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (𝟙 B) f) := by
  let a : Over B := Over.mk (f ≫ 𝟙 B)
  let b : Over B := Over.mk (𝟙 B)
  let i : a ⟶ b := Over.homMk f rfl
  let j : b ⟶ a := Over.homMk d.sectionMap (by
    change d.sectionMap ≫ (f ≫ 𝟙 B) = 𝟙 B
    rw [← Category.assoc, d.section_comp, Category.comp_id])
  change IsSimplicialHomotopyEquivalence (cofinalFunctorOverPre p i)
  refine ⟨cofinalFunctorOverPre p j, ?_, ?_⟩
  · have hji : j ≫ i = 𝟙 b := Over.OverMorphism.ext d.section_comp
    rw [← cofinalFunctorOverPre_comp, hji, cofinalFunctorOverPre_id]
    exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩
  · have hH : d.reverseHomotopy.h ≫ a.hom = fst A (Δ[1] : SSet.{u}) ≫ a.hom := by
      change d.reverseHomotopy.h ≫ (f ≫ 𝟙 B) = fst A (Δ[1] : SSet.{u}) ≫ (f ≫ 𝟙 B)
      simp only [Category.comp_id, d.reverseHomotopy_comp]
    let H := cofinalFunctorOverPreHomotopy p (i ≫ j) (𝟙 a) d.reverseHomotopy hH
    rw [← cofinalFunctorOverPre_comp]
    have hH' : Nonempty (SSet.Homotopy (cofinalFunctorOverPre p (i ≫ j))
        (cofinalFunctorOverPre p (𝟙 a))) := ⟨H⟩
    rw [cofinalFunctorOverPre_id] at hH'
    exact hH'

/-- 概要：底上の切断と収縮を持つ射は left cofinal。
方針：全ての left fibration への相対制限に明示的なホモトピー逆を与える。
規約：底は任意の単体集合。
使われ方：trivial Kan fibration の left cofinality。 -/
lemma CofinalSectionHomotopy.isLeftCofinal {A B : SSet.{u}} {f : A ⟶ B}
    (d : CofinalSectionHomotopy f) : IsLeftCofinal f := by
  intro E p hp
  exact d.restriction_isSimplicialHomotopyEquivalence p

/-- 概要：底上の切断と収縮を持つ射は right cofinal。
方針：全ての right fibration への相対制限に明示的なホモトピー逆を与える。
規約：底は任意の単体集合。
使われ方：trivial Kan fibration の right cofinality。 -/
lemma CofinalSectionHomotopy.isRightCofinal {A B : SSet.{u}} {f : A ⟶ B}
    (d : CofinalSectionHomotopy f) : IsRightCofinal f := by
  intro E p hp
  exact d.restriction_isSimplicialHomotopyEquivalence p

end SerrePositivity.InfinityCategories
