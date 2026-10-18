module

public import SerrePositivity.KST.Comparison.FatSkeletonColimit
public import SerrePositivity.KST.Comparison.FatSkeletonRowRelations
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected

/-!
# 指定した行から始まる有限骨格の順序列

概要：m 骨格から先の順序列と、m 行からの自然な射を構成する。
方針：n を m + n へ送る余終な順序関手で骨格の列を制限する。
規約：Segal 1974 Proposition 1.6 の無限骨格の行の比較。
使われ方：全ての段階で m 行が含まれる順序余極限への比較。
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
概要：自然数の順序列の m 項以降への添字の移動。
方針：加法の単調性を関手化する。
規約：第 n 項を m + n 項へ送る。
使われ方：指定した行が全ての骨格に含まれる列。
-/
def natTailFunctor (m : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ => m + n) from fun _ _ h => Nat.add_le_add_left h m).functor

/--
概要：自然数の有限個の初項を除いても余極限は変わらない。
方針：任意の添字は十分大きい m + n 以下になる。
規約：順序関手の余終性として述べる。
使われ方：骨格の尾の余極限を全体と同定する。
-/
instance natTailFunctor_final (m : ℕ) : (natTailFunctor m).Final := by
  apply (Monotone.final_functor_iff
    (show Monotone (fun n : ℕ => m + n) from fun _ _ h => Nat.add_le_add_left h m)).mpr
  intro n
  exact ⟨n, by omega⟩

/--
概要：指定した行から始まる有限骨格の順序列。
方針：元の骨格の列を添字の移動で制限する。
規約：第 n 項は m + n 骨格。
使われ方：m 行の比較の全段階への適用。
-/
def fatSkeletonTail (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (m : ℕ) : ℕ ⥤ SSet.{u} :=
  natTailFunctor m ⋙ fatSkeletonSequence F

/--
概要：骨格の尾から全体への包含の余錐。
方針：骨格全体の余錐を余終関手で制限する。
規約：頂点は元の fat realization。
使われ方：無限骨格の実際の余錐。
-/
def fatSkeletonTailCocone (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (m : ℕ) :
    Cocone (fatSkeletonTail F m) := (fatSkeletonCocone F).whisker (natTailFunctor m)

/--
概要：骨格の尾の包含の余錐も余極限である。
方針：元の骨格の余極限と余終な添字の制限を使う。
規約：具体的な fat realization を頂点に保つ。
使われ方：各行から無限骨格への四角形。
-/
def fatSkeletonTailCoconeIsColimit (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (m : ℕ) :
    IsColimit (fatSkeletonTailCocone F m) :=
  (Functor.Final.isColimitWhiskerEquiv (natTailFunctor m) (fatSkeletonCocone F)).symm
    (fatSkeletonCoconeIsColimit F)

/--
概要：元の射が骨格の尾の各段階に誘導する自然変換。
方針：全ての段階で同じ fat realization の射を部分対象へ制限する。
規約：尾の初項 m は保つ。
使われ方：各段階と無限骨格の縦射。
-/
def fatSkeletonTailMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (m : ℕ) :
    fatSkeletonTail F m ⟶ fatSkeletonTail G m where
  app n := fatSkeletonMap α (m + n)
  naturality {_ _} _ := rfl

/--
概要：m 行から m 以降の全ての骨格への自然な射。
方針：m ≤ m + n に対応する小さい行の射を各段階に取る。
規約：定義域は行と標準単体の積の定数図式。
使われ方：全段階の四角形の順序余極限への適用。
-/
def fatSkeletonTailRow (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (m : ℕ) :
    (Functor.const ℕ).obj (F.obj (op ⦋m⦌) ⊗ Δ[m]) ⟶ fatSkeletonTail F m where
  app n := fatSkeletonRowOfLE F (Nat.le_add_right m n)
  naturality {_ _} _ := rfl

/--
概要：骨格の尾への各行の射は二重単体集合の射について自然。
方針：各段階で指定骨格への行の自然性を使う。
規約：図式圏の可換四角形として記録する。
使われ方：順序余極限のホモトピー引き戻しの比較。
-/
theorem fatSkeletonTailRow_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (α : F ⟶ G) (m : ℕ) :
    fatSkeletonTailRow F m ≫ fatSkeletonTailMap α m =
      (Functor.const ℕ).map (α.app (op ⦋m⦌) ▷ Δ[m]) ≫ fatSkeletonTailRow G m := by
  apply NatTrans.ext
  funext n
  exact fatSkeletonRowOfLE_map α (Nat.le_add_right m n)

end SerrePositivity.KST.Comparison
