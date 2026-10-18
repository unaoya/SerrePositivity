module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-!
# 二重単体的集合の方向の交換と対角

概要：二つの単体方向を交換しても対角は標準同型で一致する。
方針：各対象では恒等同型、単体射では元の自然性を使う。
規約：KST Proposition A.1 と GJ99 Proposition IV.1.9 の局所化模型。
使われ方：bar の各行の可逆性を実際の対角比較へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory SerrePositivity.BisimplicialModel

/-- 概要：二つの単体方向を交換した対角と元の対角の同型。
方針：各次数の恒等同型の自然性を二重図式の自然性で示す。
規約：KST Proposition A.1。使われ方：行ごとの同値性の対角への移送。 -/
def bisimplicialDiagonalFlipIso (X : SimplicialObject SSet.{u}) :
    diagonal.obj X.flip ≅ diagonal.obj X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m f
    change (X.obj n).map f ≫ (X.map f).app m ≫ 𝟙 _ =
      𝟙 _ ≫ (X.map f).app n ≫ (X.obj m).map f
    simp only [Category.comp_id, Category.id_comp]
    exact (X.map f).naturality f)

/-- 概要：対角の方向交換の同型は二重単体的写像に自然。
方針：各次数の恒等射と比較写像の成分を評価する。
規約：KST Proposition A.1。使われ方：flip の対角での可逆性を元の対角へ移す。 -/
theorem bisimplicialDiagonalFlipIso_naturality {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    (bisimplicialDiagonalFlipIso X).hom ≫ diagonal.map f =
      diagonal.map ((flipFunctor _ _ _).map f) ≫ (bisimplicialDiagonalFlipIso Y).hom := by
  rfl

/-- 概要：方向を交換した各行が局所化で可逆なら元の対角も可逆。
方針：既存の行ごとの局所化同値の対角定理と方向交換同型を使う。
規約：KST Proposition A.1、GJ99 Proposition IV.1.9 の局所化模型。
使われ方：原典の各行の比較から対角の比較へ進む。 -/
theorem localized_diagonal_map_of_flipped_rows {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ n, IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (((flipFunctor _ _ _).map f).app n))) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (diagonal.map f)) := by
  let Q := SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ
  haveI := localized_diagonal_map ((flipFunctor _ _ _).map f) hf
  have hn := congrArg Q.map (bisimplicialDiagonalFlipIso_naturality f)
  simp only [CategoryTheory.Functor.map_comp] at hn
  have hc : IsIso (Q.map (bisimplicialDiagonalFlipIso X).hom ≫ Q.map (diagonal.map f)) :=
    hn.symm ▸ inferInstanceAs (IsIso
      (Q.map (diagonal.map ((flipFunctor _ _ _).map f)) ≫
        Q.map (bisimplicialDiagonalFlipIso Y).hom))
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.ProExcision
