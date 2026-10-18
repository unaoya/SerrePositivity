module

public import SerrePositivity.InfinityCategories.F1B.CofinalFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1B.CofinalWeakEquivalence

/-!
概要：cofinality の任意の底図式への適用と合成。
方針：検査する fibration を底図式へ引き戻し、相対関手空間の厳密な同型で戻す。
規約：始域・終域の充填性を仮定せず、元の相対制限写像の同値性を得る。
使われ方：Kerodon Proposition 7.2.1.6、Quillen A の因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：left cofinal な制限は任意の底図式の相対関手空間でも同値。
方針：底図式へ引き戻した fibration に定義を適用し、底変換の同型で移す。
規約：元の底 B から検査する底 C への図式 a は任意。
使われ方：Kerodon Proposition 7.2.1.6、cofinality の合成。 -/
lemma IsLeftCofinal.restrictDiagram {A B C E : SSet.{u}} {i : A ⟶ B}
    (hi : IsLeftCofinal i) (p : E ⟶ C) [LeftFibration p] (a : B ⟶ C) :
    IsSimplicialHomotopyEquivalence (cofinalFunctorPre p a i) := by
  have : LeftFibration (pullback.snd p a) :=
    ⟨leftFibrations.pullback_snd p a (LeftFibration.mem (p := p))⟩
  have h := (hi (pullback p a) (pullback.snd p a)).isQCatEquivalence.comp
    (qCatEquivalenceOfIso (cofinalFunctorBaseChangeIso p a (i ≫ 𝟙 B))).isQCatEquivalence
  change IsQCatEquivalence (cofinalFunctorPre (pullback.snd p a) (𝟙 B) i ≫
    (cofinalFunctorBaseChangeIso p a (i ≫ 𝟙 B)).hom) at h
  rw [← cofinalFunctorBaseChangeIso_pre] at h
  have he : IsQCatEquivalence (cofinalFunctorBaseChangeIso p a (𝟙 B)).hom :=
    (qCatEquivalenceOfIso (cofinalFunctorBaseChangeIso p a (𝟙 B))).isQCatEquivalence
  have hr : IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (𝟙 B ≫ a) i) :=
    (he.cancel_left h).isSimplicialHomotopyEquivalence
  exact (Category.id_comp a) ▸ hr

/-- 概要：left cofinal な射の合成は left cofinal。
方針：第二の射の制限に続けて、第一の射を任意の底図式へ適用する。
規約：i の後に j を合成する。
使われ方：Kerodon Proposition 7.2.1.6。 -/
lemma IsLeftCofinal.comp {A B C : SSet.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : IsLeftCofinal i) (hj : IsLeftCofinal j) : IsLeftCofinal (i ≫ j) := by
  intro E p hp
  have ht : IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (j ≫ 𝟙 C) i) := by
    exact hi.restrictDiagram p (j ≫ 𝟙 C)
  have h := (hj E p).comp ht
  rw [cofinalFunctorPre_comp] at h
  exact h

/-- 概要：i と i≫j が left cofinal なら j は left cofinal。
方針：任意の底図式に適用した i の制限を、合成の同値性から消去する。
規約：逆の消去則は主張しない。
使われ方：Kerodon Proposition 7.2.1.6 の因子分解。 -/
lemma IsLeftCofinal.cancel_left {A B C : SSet.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : IsLeftCofinal i) (hij : IsLeftCofinal (i ≫ j)) : IsLeftCofinal j := by
  intro E p hp
  have ht : IsQCatEquivalence (cofinalFunctorPre p (j ≫ 𝟙 C) i) := by
    exact (hi.restrictDiagram p (j ≫ 𝟙 C)).isQCatEquivalence
  have hh := (hij E p).isQCatEquivalence
  rw [← cofinalFunctorPre_comp p (𝟙 C) j i] at hh
  exact (ht.cancel_right hh).isSimplicialHomotopyEquivalence

/-- 概要：right cofinal な制限は任意の底図式の相対関手空間でも同値。
方針：底図式へ引き戻した fibration に定義を適用し、底変換の同型で移す。
規約：元の底 B から検査する底 C への図式 a は任意。
使われ方：Kerodon Proposition 7.2.1.6、cofinality の合成。 -/
lemma IsRightCofinal.restrictDiagram {A B C E : SSet.{u}} {i : A ⟶ B}
    (hi : IsRightCofinal i) (p : E ⟶ C) [RightFibration p] (a : B ⟶ C) :
    IsSimplicialHomotopyEquivalence (cofinalFunctorPre p a i) := by
  have : RightFibration (pullback.snd p a) :=
    ⟨rightFibrations.pullback_snd p a (RightFibration.mem (p := p))⟩
  have h := (hi (pullback p a) (pullback.snd p a)).isQCatEquivalence.comp
    (qCatEquivalenceOfIso (cofinalFunctorBaseChangeIso p a (i ≫ 𝟙 B))).isQCatEquivalence
  change IsQCatEquivalence (cofinalFunctorPre (pullback.snd p a) (𝟙 B) i ≫
    (cofinalFunctorBaseChangeIso p a (i ≫ 𝟙 B)).hom) at h
  rw [← cofinalFunctorBaseChangeIso_pre] at h
  have he : IsQCatEquivalence (cofinalFunctorBaseChangeIso p a (𝟙 B)).hom :=
    (qCatEquivalenceOfIso (cofinalFunctorBaseChangeIso p a (𝟙 B))).isQCatEquivalence
  have hr : IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (𝟙 B ≫ a) i) :=
    (he.cancel_left h).isSimplicialHomotopyEquivalence
  exact (Category.id_comp a) ▸ hr

/-- 概要：right cofinal な射の合成は right cofinal。
方針：第二の射の制限に続けて、第一の射を任意の底図式へ適用する。
規約：i の後に j を合成する。
使われ方：Kerodon Proposition 7.2.1.6。 -/
lemma IsRightCofinal.comp {A B C : SSet.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : IsRightCofinal i) (hj : IsRightCofinal j) : IsRightCofinal (i ≫ j) := by
  intro E p hp
  have ht : IsSimplicialHomotopyEquivalence (cofinalFunctorPre p (j ≫ 𝟙 C) i) := by
    exact hi.restrictDiagram p (j ≫ 𝟙 C)
  have h := (hj E p).comp ht
  rw [cofinalFunctorPre_comp] at h
  exact h

/-- 概要：i と i≫j が right cofinal なら j は right cofinal。
方針：任意の底図式に適用した i の制限を、合成の同値性から消去する。
規約：逆の消去則は主張しない。
使われ方：Kerodon Proposition 7.2.1.6 の因子分解。 -/
lemma IsRightCofinal.cancel_left {A B C : SSet.{u}} {i : A ⟶ B} {j : B ⟶ C}
    (hi : IsRightCofinal i) (hij : IsRightCofinal (i ≫ j)) : IsRightCofinal j := by
  intro E p hp
  have ht : IsQCatEquivalence (cofinalFunctorPre p (j ≫ 𝟙 C) i) := by
    exact (hi.restrictDiagram p (j ≫ 𝟙 C)).isQCatEquivalence
  have hh := (hij E p).isQCatEquivalence
  rw [← cofinalFunctorPre_comp p (𝟙 C) j i] at hh
  exact (ht.cancel_right hh).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
