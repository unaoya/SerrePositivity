module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Composition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Identity
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：quasicategory と関手の同型類からなるホモトピー圏。
方針：関手単体集合のホモトピー圏で同型な射を同値関係として商を取る。
規約：対象は小さな quasicategory、射は単体集合の射の FunctorIso による類。
使われ方：Kerodon Construction 4.5.1.1（Tag 01DR）、Construction 5.2.5.2（Tag 019U） の transport の標的。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：関手を可逆な二胞体で同一視する同値関係。
方針：関手単体集合のホモトピー圏の同型の存在を使う。
規約：始域・終域の quasicategory 性はこの同値関係自体には不要。
使われ方：Kerodon Construction 4.5.1.1（Tag 01DR）、関手の同型類の定義。 -/
@[kerodon 01DR]
def homotopyQCatHomSetoid (X Y : SSet.{u}) : Setoid (X ⟶ Y) where
  r f g := Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
  iseqv := ⟨fun _ ↦ ⟨Iso.refl _⟩, fun ⟨h⟩ ↦ ⟨h.symm⟩,
    fun ⟨h⟩ ⟨k⟩ ↦ ⟨h ≪≫ k⟩⟩

/-- 概要：quasicategory のホモトピー圏の対象。
方針：単体集合とその内ホーン充填性をまとめる。
規約：obj は宇宙 u の単体集合。
使われ方：Kerodon Construction 4.5.1.1（Tag 01DR）、Construction 5.2.5.2（Tag 019U） の fiber の値。 -/
@[kerodon 01DR]
structure HomotopyQCat where
  /-- 対象の単体集合。 -/
  obj : SSet.{u}
  /-- 対象は quasicategory。 -/
  isQuasicategory : Quasicategory obj

attribute [instance] HomotopyQCat.isQuasicategory

/-- 概要：quasicategory の関手の同型類は圏をなす。
方針：前後合成が FunctorIso を保つことから商の合成を定義する。
規約：関手の合成は左から右。
使われ方：Kerodon Construction 4.5.1.1（Tag 01DR）、ホモトピー transport 表現の標的の圏構造。 -/
@[kerodon 01DR]
instance homotopyQCat_category : Category HomotopyQCat.{u} where
  Hom X Y := Quotient (homotopyQCatHomSetoid X.obj Y.obj)
  id X := Quotient.mk _ (𝟙 X.obj)
  comp := Quotient.map₂ (fun f g ↦ f ≫ g) (by
    intro f f' hf g g' hg
    obtain ⟨hf⟩ := hf
    obtain ⟨hg⟩ := hg
    exact ⟨hf.postcomp g ≪≫ hg.precomp f'⟩)
  id_comp := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f => exact congrArg (Quotient.mk _) (Category.id_comp f)
  comp_id := by
    intro X Y f
    induction f using Quotient.inductionOn with
    | _ f => exact congrArg (Quotient.mk _) (Category.comp_id f)
  assoc := by
    intro W X Y Z f g h
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
        induction h using Quotient.inductionOn with
        | _ h => exact congrArg (Quotient.mk _) (Category.assoc f g h)

/-- 概要：単体集合の射を quasicategory のホモトピー圏の射にする。
方針：関手の同型類を取る。
規約：対象の束縛された単体集合の間の射を入力する。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、辺の transport 関手の類。 -/
def homotopyQCatHomMk {X Y : HomotopyQCat.{u}} (f : X.obj ⟶ Y.obj) : X ⟶ Y :=
  Quotient.mk _ f

/-- 概要：関手の可逆な二胞体はホモトピー圏の射の等式を与える。
方針：商の同値関係を適用する。
規約：同型のデータの非空性だけを要求する。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、transport の恒等則・合成則。 -/
lemma homotopyQCatHomMk_eq_of_functorIso {X Y : HomotopyQCat.{u}}
    {f g : X.obj ⟶ Y.obj} (h : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)) :
    homotopyQCatHomMk f = homotopyQCatHomMk g := Quotient.sound h

/-- 概要：ホモトピー圏の射への移行は合成を保つ。
方針：商上の合成の定義を展開する。
規約：射を代表元で与える。
使われ方：Kerodon Construction 5.2.5.2（Tag 019U）、辺の合成に関する関手則。 -/
lemma homotopyQCatHomMk_comp {X Y Z : HomotopyQCat.{u}}
    (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    homotopyQCatHomMk (f ≫ g) = homotopyQCatHomMk f ≫ homotopyQCatHomMk g := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
