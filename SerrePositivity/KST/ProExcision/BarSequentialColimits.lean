module
public import SerrePositivity.KST.ProExcision.BarFinitePower
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Category.MonCat.Colimits

/-!
# 実対角 bar の順序余極限保存

概要：単体的モノイドの対角 bar が通常の rank 余極限を保存することを証明する。
方針：各次数で有限個のモノイド座標の共変 Hom と自然に比較する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。遷移射の単射性は不要。
使われ方：有限 rank の実ホモロジーと安定モノイドの実 bar の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits Opposite

/-- 概要：実対角 bar の指定次数を有限座標の共変 Hom と比較する実自然同型。
方針：実 Segal 座標と ULift による添字宇宙の同定を合成する。
規約：SW92 Lemma 1.4 の有限性。使われ方：順序余極限の各次数での保存。 -/
def monoidBarDegreeIso (k : SimplexCategoryᵒᵖ) :
    monoidBarFunctor.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj k ≅
      (evaluation SimplexCategoryᵒᵖ MonCat.{u}).obj k ⋙ forget MonCat ⋙
        coyoneda.obj (op (ULift.{u} (Fin k.unop.len))) :=
  NatIso.ofComponents (fun M ↦ Equiv.toIso
    ((Comparison.monoidWordEquiv (M.obj k) k.unop.len).trans {
      toFun := fun v ↦ TypeCat.ofHom (fun i ↦ v i.down)
      invFun := fun f i ↦
        (show ULift.{u} (Fin k.unop.len) ⟶ (forget MonCat).obj (M.obj k) from f) ⟨i⟩
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro f
        apply ConcreteCategory.hom_ext
        intro i
        cases i
        rfl })) (by
      intro M N f
      apply ConcreteCategory.hom_ext
      intro F
      apply ConcreteCategory.hom_ext
      intro i
      rfl)

/-- 概要：実対角 bar は自然数添字の余極限を保存する。
方針：モノイドの忘却と有限座標の共変 Hom の filtered colimit 保存を各次数に適用する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。保存性を新たな入力にしない。
使われ方：通常の安定 rank の bar と有限 rank の bar の実同定。 -/
instance monoidBarFunctor_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ monoidBarFunctor.{u} := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget MonCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply preservesColimitsOfShape_of_evaluation
  intro k
  letI := finitePower_preservesSequentialColimits.{u} k.unop.len
  exact preservesColimitsOfShape_of_natIso (monoidBarDegreeIso k).symm

/-- 概要：実安定モノイドの bar と有限 rank の bar の余極限の実同型。
方針：実証明した順序余極限保存の標準比較同型を使う。
規約：SW92 Lemma 1.4。使われ方：安定 H_* への実模型比較。 -/
def monoidBarSequentialColimitIso (D : ℕ ⥤ SimplicialObject MonCat.{u}) :
    Comparison.monoidBar (colimit D) ≅ colimit (D ⋙ monoidBarFunctor) :=
  preservesColimitIso monoidBarFunctor D

end SerrePositivity.KST.ProExcision
