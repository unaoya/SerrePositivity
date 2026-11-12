module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-!
概要：辺のホモトピー類の圏の関手性と比較同値の自然性。
方針：辺と二単体を写し、商の代表元上で法則を検証する。
規約：Mathlib の quasicategory のみを仮定し、射の充填保存を別仮定にしない。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピー圏の関手性。

対応節は Kerodon 1.4（Tag 0039）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet SSet.Truncated SimplicialObject.Truncated

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

variable {X Y Z : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]

/-- 概要：単体集合の射が辺の類の圏に誘導する関手。
方針：辺を写し、左ホモトピーと合成二単体の像により商と合成を保存する。
規約：始域・終域は quasicategory。射自体への追加仮定はない。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の関手性。 -/
noncomputable def map (f : X ⟶ Y) :
    HomotopyCategory₂ ((truncation 2).obj X) ⥤
      HomotopyCategory₂ ((truncation 2).obj Y) where
  obj x := ⟨((truncation 2).map f).app _ x.pt⟩
  map := Quotient.lift (fun e ↦ HomotopyCategory₂.homMk (e.map ((truncation 2).map f)))
    (fun _ _ h ↦ (show HomotopicL _ _ from
      ⟨by simpa using! h.some.map ((truncation 2).map f)⟩).congr_homotopyCategory₂HomMk)
  map_id x := by
    change HomotopyCategory₂.homMk ((SSet.Truncated.Edge.id x.pt).map ((truncation 2).map f)) = _
    rw [SSet.Truncated.Edge.map_id]
    rfl
  map_comp := by
    rintro _ _ _ ⟨e⟩ ⟨e'⟩
    exact ((Edge.compStruct e e').map ((truncation 2).map f)).homotopyCategory₂_fac.symm

/-- 概要：誘導関手は恒等射を恒等関手に送る。
方針：辺の商の代表元で計算する。規約：quasicategory の恒等射。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の関手法則。 -/
lemma map_id : map (𝟙 X) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  rintro _ _ ⟨e⟩
  simp [map, HomotopyCategory₂.homMk]
  rfl

/-- 概要：誘導関手は単体集合の射の合成を保つ。
方針：辺の像の二重適用を計算する。規約：合成の順は `≫` と `⋙`。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の関手法則。 -/
lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ⋙ map g := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  rintro _ _ ⟨e⟩
  simp [map, HomotopyCategory₂.homMk]
  rfl

/-- 概要：A1a の比較同値の順関手は単体集合の射について自然。
方針：辺の類の代表元で両辺を計算する。規約：等式は関手の等式。
使われ方：HTT §1.2.3、Kerodon Proposition 1.4.5.7（Tag 004H） の比較の自然性。 -/
lemma bridge_naturality (f : X ⟶ Y) :
    map f ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge Y).functor =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor ⋙ (hoFunctor.map f).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  rintro _ _ ⟨e⟩
  change SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f)) =
    (SSet.Truncated.mapHomotopyCategory ((truncation 2).map f)).map
      (SSet.Truncated.HomotopyCategory.homMk e)
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
