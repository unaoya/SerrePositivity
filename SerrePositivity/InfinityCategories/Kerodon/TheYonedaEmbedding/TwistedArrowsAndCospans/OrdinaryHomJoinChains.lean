module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomElements
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Join.Basic

/-!
概要：通常の Hom の元の圏の射列を、逆向きの源の列と順向きの標的の列の join として読む。
方針：最初の射を中心に置き、元の射列の二成分で全ての交差射を作る。
規約：中心の射・両端・各対角の射を同じ指定資料のまま保持する。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）の鎖の表示、
HTT 5.1.5.6 の S8 の指定 Yoneda 比較の証明分割。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {n : ℕ}

/-- 指定射列の源を逆向きに読む既存の反対関手。
Kerodon Proposition 8.1.1.10（Tag 03JN）、join の左側の全射列。 -/
def ordinaryHomSourceChain (s : ComposableArrows (OrdinaryHomElements C) n) :
    (Fin (n + 1))ᵒᵖ ⥤ C :=
  (s ⋙ ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.fst Cᵒᵖ C).leftOp

/-- 指定射列の標的を同じ向きに読む関手。
Kerodon Proposition 8.1.1.10（Tag 03JN）、join の右側の全射列。 -/
def ordinaryHomTargetChain (s : ComposableArrows (OrdinaryHomElements C) n) :
    Fin (n + 1) ⥤ C := s ⋙ ordinaryHomElementsProjection C ⋙ CategoryTheory.Prod.snd Cᵒᵖ C

/-- 元の最初の射と二つの端点の列から作る、join の全交差射。
Kerodon Proposition 8.1.1.10（Tag 03JN）、両変数で自然な同じ射の族。 -/
def ordinaryHomCrossChain (s : ComposableArrows (OrdinaryHomElements C) n) :
    CategoryTheory.Prod.fst (Fin (n + 1))ᵒᵖ (Fin (n + 1)) ⋙ ordinaryHomSourceChain s ⟶
      CategoryTheory.Prod.snd (Fin (n + 1))ᵒᵖ (Fin (n + 1)) ⋙ ordinaryHomTargetChain s where
  app ij := (s.map (homOfLE (Fin.zero_le ij.1.unop))).hom.1.unop ≫
    (s.obj 0).val ≫ (s.map (homOfLE (Fin.zero_le ij.2))).hom.2
  naturality {a b} h := by
    have hs : (s.map (homOfLE (Fin.zero_le a.1.unop))).hom.1.unop =
        (s.map h.1.unop).hom.1.unop ≫
          (s.map (homOfLE (Fin.zero_le b.1.unop))).hom.1.unop := by
      have hi : homOfLE (Fin.zero_le a.1.unop) =
          homOfLE (Fin.zero_le b.1.unop) ≫ h.1.unop := Subsingleton.elim _ _
      rw [hi, s.map_comp]
      rfl
    have ht : (s.map (homOfLE (Fin.zero_le b.2))).hom.2 =
        (s.map (homOfLE (Fin.zero_le a.2))).hom.2 ≫ (s.map h.2).hom.2 := by
      have hi : homOfLE (Fin.zero_le b.2) =
          homOfLE (Fin.zero_le a.2) ≫ h.2 := Subsingleton.elim _ _
      rw [hi, s.map_comp]
      rfl
    change (s.map h.1.unop).hom.1.unop ≫
        ((s.map (homOfLE (Fin.zero_le b.1.unop))).hom.1.unop ≫
          (s.obj 0).val ≫ (s.map (homOfLE (Fin.zero_le b.2))).hom.2) =
      ((s.map (homOfLE (Fin.zero_le a.1.unop))).hom.1.unop ≫
        (s.obj 0).val ≫ (s.map (homOfLE (Fin.zero_le a.2))).hom.2) ≫
          (s.map h.2).hom.2
    rw [← Category.assoc (s.map h.1.unop).hom.1.unop
      (s.map (homOfLE (Fin.zero_le b.1.unop))).hom.1.unop, ← hs, ht]
    simp only [Category.assoc]

/-- 全交差射を持つ同じ join 図式。元の圏の join の既存の普遍構成を使う。
Kerodon Proposition 8.1.1.10（Tag 03JN）、単体的比較への通常圏側の入力。 -/
def ordinaryHomJoinChain (s : ComposableArrows (OrdinaryHomElements C) n) :
    CategoryTheory.Join (Fin (n + 1))ᵒᵖ (Fin (n + 1)) ⥤ C :=
  CategoryTheory.Join.mkFunctor (ordinaryHomSourceChain s) (ordinaryHomTargetChain s)
    (ordinaryHomCrossChain s)

/-- 指定した交差射の対角は、元の射列の同じ各対象の射に一致する。
Kerodon Proposition 8.1.1.10（Tag 03JN）、中心だけに制限しない計算則。 -/
lemma ordinaryHomCrossChain_diagonal (s : ComposableArrows (OrdinaryHomElements C) n)
    (i : Fin (n + 1)) : (ordinaryHomCrossChain s).app (Opposite.op i, i) = (s.obj i).val :=
  ordinaryHomElements_map_val (s.map (homOfLE (Fin.zero_le i)))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
