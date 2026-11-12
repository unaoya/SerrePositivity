module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.DoubleSubdivisionHornBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.DoubleSubdivisionAdjunction

/-!
# 二回の Ex の後での horn の充填

概要：horn から任意の単体集合への写像は、二回の Ex の単位を合成した後に標準単体へ延長できる。
方針：二重細分から horn への具体的な写像を随伴で転置し、境界条件を単位の反復へ移す。
規約：Moss 2020 Proposition 21 の Kan 性に用いる有限段階の充填。
使われ方：有限な horn の写像を反復列の有限段階で充填する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory
open scoped _root_.Simplicial

/--
概要：horn の恒等写像を二回の Ex の適用後に標準単体へ延長する写像。
方針：二重細分から horn への具体的な写像を二回の随伴で転置する。
規約：正次元の horn を扱う。
使われ方：任意の単体集合への horn の写像を充填する普遍的な候補。
-/
def exDoubleUniversalHornFiller (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    (Δ[n] : SSet.{u}) ⟶ SSet.ex.obj (SSet.ex.obj (SSet.horn n k)) :=
  doubleSubdivisionHomEquiv _ _ (doubleSubdivisionHornMap n hn k)

/--
概要：普遍的な充填の horn 上の制限は Ex の単位の二回の合成である。
方針：二重細分の境界条件を随伴で転置する。
規約：Moss 2020 Proposition 21 の有限段階の充填の境界条件。
使われ方：単位の反復で延長する写像であることの証明。
-/
@[reassoc] theorem exDoubleUniversalHornFiller_boundary (n : ℕ) (hn : 0 < n)
    (k : Fin (n + 1)) :
    (SSet.horn.{u} n k).ι ≫ exDoubleUniversalHornFiller n hn k =
      exUnitAt (SSet.horn n k) ≫ exUnitAt (SSet.ex.obj (SSet.horn n k)) := by
  rw [exDoubleUniversalHornFiller, ← doubleSubdivisionHomEquiv_naturality_left,
    doubleSubdivisionHornMap_boundary, doubleSubdivisionHomEquiv_lastVertex]

/--
概要：任意の horn の写像を二回の Ex の適用後に充填する具体的な写像。
方針：普遍的な充填に二回の Ex を適用した元の写像を後合成する。
規約：まだ Ex∞ の Kan 性ではなく、各有限段階の延長を与える。
使われ方：反復列の余極限での Kan 性。
-/
def exDoubleHornFiller (X : SSet.{u}) (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (f : (SSet.horn n k : SSet.{u}) ⟶ X) : Δ[n] ⟶ SSet.ex.obj (SSet.ex.obj X) :=
  exDoubleUniversalHornFiller n hn k ≫ SSet.ex.map (SSet.ex.map f)

/--
概要：任意の horn の具体的な充填は、元の写像に Ex の単位を二回合成したものを延長する。
方針：普遍的な境界条件と単位の自然性を二回使う。
規約：Moss 2020 Proposition 21 の有限段階の充填。
使われ方：余極限へ合成して horn の充填を得る。
-/
@[reassoc] theorem exDoubleHornFiller_boundary (X : SSet.{u}) (n : ℕ) (hn : 0 < n)
    (k : Fin (n + 1)) (f : (SSet.horn n k : SSet.{u}) ⟶ X) :
    (SSet.horn n k).ι ≫ exDoubleHornFiller X n hn k f =
      f ≫ exUnitAt X ≫ exUnitAt (SSet.ex.obj X) := by
  rw [exDoubleHornFiller, exDoubleUniversalHornFiller_boundary_assoc]
  rw [← exUnitAt_naturality (SSet.ex.map f), ← Category.assoc, ← exUnitAt_naturality f]
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
