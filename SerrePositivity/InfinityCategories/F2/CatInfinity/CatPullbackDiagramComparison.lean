module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackReplacementCone
public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictCoherentNatTransComponent

/-!
概要：元の cospan と可逆 path で置換した cospan の Cat_∞ 内での同型。
方針：定値 path の切断を自然変換に束ね、全成分の同値性を使う。
規約：引き戻しの候補を変えず、図式の比較を実際に構成する。
使われ方：Cat_∞ の元の二関手の引き戻しの極限錐への輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]

/-- 概要：元の二つの関手による QCat の小さい cospan 図式。
方針：三つの quasicategory を束縛し、AsSmall で添字を持ち上げる。
規約：p、q に fibration 性を要求しない。
使われ方：構成すべき Cat_∞ の引き戻しの元の図式。 -/
def catPullbackDiagram (p : A ⟶ C) (q : B ⟶ C) :
    AsSmall.{u} WalkingCospan ⥤ QCat.{u} :=
  let A₀ : QCat.{u} := (⟨A, inferInstance⟩ : QuasicategoryObject.{u})
  let B₀ : QCat.{u} := (⟨B, inferInstance⟩ : QuasicategoryObject.{u})
  let C₀ : QCat.{u} := (⟨C, inferInstance⟩ : QuasicategoryObject.{u})
  qCatPullbackDiagram (show A₀ ⟶ C₀ from p) (show B₀ ⟶ C₀ from q)
/-- 概要：定値 path の切断は元と置換後の cospan の自然変換を与える。
方針：第一対象で切断、残る二対象で恒等射を使う。
規約：自然性は切断と終点関手の合成の厳密な等式による。
使われ方：置換後の極限錐を元の図式に戻す比較。 -/
def catPullbackReplacementNatTrans (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackDiagram p q ⟶ catPullbackReplacementDiagram p q := by
  let A₀ : QCat.{u} := (⟨A, inferInstance⟩ : QuasicategoryObject.{u})
  let E₀ : QCat.{u} := (⟨equivalencePathReplacement p, inferInstance⟩ : QuasicategoryObject.{u})
  let B₀ : QCat.{u} := (⟨B, inferInstance⟩ : QuasicategoryObject.{u})
  let C₀ : QCat.{u} := (⟨C, inferInstance⟩ : QuasicategoryObject.{u})
  let η : cospan (show A₀ ⟶ C₀ from p) (show B₀ ⟶ C₀ from q) ⟶
      cospan (show E₀ ⟶ C₀ from equivalencePathReplacementMap p) (show B₀ ⟶ C₀ from q) :=
    cospanHomMk (𝟙 C₀) (show A₀ ⟶ E₀ from equivalencePathReplacementSection p) (𝟙 B₀)
      (by
        change p ≫ 𝟙 C = equivalencePathReplacementSection p ≫ equivalencePathReplacementMap p
        rw [Category.comp_id, equivalencePathReplacementSection_map])
      (by simp)
  exact CategoryTheory.Functor.whiskerLeft
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) η
/-- 概要：cospan の比較自然変換の全成分は quasicategory の同値。
方針：第一対象では切断の同値性、残る二対象では恒等同値を使う。
規約：各元の成分の同値性を述べる。
使われ方：coherent な図式全体の同型の構成。 -/
lemma catPullbackReplacementNatTrans_isEquivalence (p : A ⟶ C) (q : B ⟶ C)
    (i : AsSmall.{u} WalkingCospan) :
    IsQCatEquivalence ((catPullbackReplacementNatTrans p q).app i) := by
  rcases i with ⟨_ | ⟨_ | _⟩⟩
  · change IsQCatEquivalence (𝟙 C)
    exact (QCatEquivalence.refl C).isQCatEquivalence
  · change IsQCatEquivalence (equivalencePathReplacementSection p)
    exact F1B.kanEquivalencePathReplacementSection_isQCatEquivalence p
  · change IsQCatEquivalence (𝟙 B)
    exact (QCatEquivalence.refl B).isQCatEquivalence
/-- 概要：元と path 置換後の cospan は Cat_∞ 値図式として同型。
方針：比較自然変換の全成分の同値性を coherent 円柱へ送る。
規約：元の p、q と置換後の指定図式との関手同型。
使われ方：置換後の native な極限錐の元の図式への輸送。 -/
def catPullbackReplacementDiagramIso (p : A ⟶ C) (q : B ⟶ C) :
    FunctorIso (HomotopyLimits.strictCoherentDiagram (catPullbackDiagram p q))
      (HomotopyLimits.strictCoherentDiagram (catPullbackReplacementDiagram p q)) := by
  apply strictCoherentNatTransIso (catPullbackReplacementNatTrans p q)
  intro i
  exact (catInfinityEdge_isInvertible_iff _).mpr
    (catPullbackReplacementNatTrans_isEquivalence p q i)

end SerrePositivity.InfinityCategories.F2
