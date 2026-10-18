module

public import SerrePositivity.KST.Comparison.ActionBarSquares
public import SerrePositivity.KST.Comparison.RegularBarProjection
public import SerrePositivity.KST.Comparison.CylinderBoundary

/-!
# 正則 bar 束の第零行の同定

概要：正則 bar の第零行を元のモノイド、基底の第零行を一点と同定する。
方針：長さ零の射列は対象の指定だけであることを使う。
規約：Segal 1974 Propositions 1.5・1.6 の基点上のファイバー。
使われ方：realization の第零行の四角形を標準ファイバーの四角形へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：正則 bar の第零行はモノイドの基礎単体集合と同型。
方針：長さ零の射列の唯一の対象の値を読み、定数の射列で戻す。
規約：群状性は不要。
使われ方：realization の第零行のファイバー。
-/
def regularBarZeroRowIso (M : SimplicialObject MonCat.{u}) :
    (actionBarTotal M).obj (op ⦋0⦌) ≅ monoidSpace M :=
  NatIso.ofComponents (fun d => Equiv.toIso
    { toFun := fun E => (E.obj 0).val
      invFun := fun m => ComposableArrows.mk₀ (RegularAction.mk m)
      left_inv := fun E => by
        obtain ⟨a, rfl⟩ := ComposableArrows.mk₀_surjective E
        rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

/--
概要：任意の単体集合から bar の第零行への標準写像。
方針：各次数で一対象圏の唯一の長さ零の射列を選ぶ。
規約：入力の単体には依存しない。
使われ方：第零行の終対象としての普遍性。
-/
def monoidBarZeroRowMap (M : SimplicialObject MonCat.{u}) (X : SSet.{u}) :
    X ⟶ (actionBarBase M).obj (op ⦋0⦌) where
  app d := TypeCat.ofHom (fun _ => ComposableArrows.mk₀ (SingleObj.star (M.obj d)))
  naturality {d e} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (1 : M.obj e) = (M.map θ).hom 1
    exact (map_one _).symm

/--
概要：bar の第零行は終対象である。
方針：一対象圏の長さ零の射列の一意性を使う。
規約：自然な単体集合としての終対象。
使われ方：第零行を標準零単体と同定する。
-/
def monoidBarZeroRowIsTerminal (M : SimplicialObject MonCat.{u}) :
    IsTerminal ((actionBarBase M).obj (op ⦋0⦌)) :=
  IsTerminal.ofUniqueHom (monoidBarZeroRowMap M) (fun X f => by
        apply NatTrans.ext
        funext d
        apply ConcreteCategory.hom_ext
        intro x
        obtain ⟨a, ha⟩ := ComposableArrows.mk₀_surjective (f.app d x)
        change f.app d x = ComposableArrows.mk₀ (SingleObj.star (M.obj d))
        rw [ha]
        have ha' : (show SingleObj (M.obj d) from a) = SingleObj.star (M.obj d) :=
          Subsingleton.elim _ _
        exact congrArg ComposableArrows.mk₀ ha')

/--
概要：bar の第零行と標準零単体との同型。
方針：二つの終対象の普遍性で同型を取る。
規約：標準零単体への射は一意な射。
使われ方：bar の基点を含む四角形への移送。
-/
def monoidBarZeroRowIso (M : SimplicialObject MonCat.{u}) :
    (actionBarBase M).obj (op ⦋0⦌) ≅ (Δ[0] : SSet.{u}) :=
  (monoidBarZeroRowIsTerminal M).uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

end SerrePositivity.KST.Comparison
