module
public import SerrePositivity.KST.SConstruction.MultiSimplicial

/-! # 多単体的 S 構成の自然性と対角実現
概要：有限反復の全多単体構造を安定な入力について関手化し、対角実現を取る。
方針：評価・前後合成・uncurry・対角の既存の関手を合成する。
規約：対角を Kan と主張しない。使われ方：反復 S• の連結スペクトルの空間模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：多単体的反復 S は安定な入力について関手的。
方針：評価を多単体的自己関手で前合成して底の単体集合へ忘れる。
規約：全方向の作用と入力の射の自然性を含む。使われ方：K の関手性。 -/
def multiSConstructionFunctor (r : ℕ) :
    StableModel.{u} ⥤ ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :=
  evaluation StableModel.{u} StableModel.{u} ⋙
    (Functor.whiskeringLeft _ _ _).obj (multiSEndofunctor r) ⋙
      (Functor.whiskeringRight _ _ _).obj stableModelForget

/-- 概要：反復 S の関手の各入力での値は既存の多単体構造。
方針：評価関手を展開する。
規約：厳密な等号。使われ方：既存対象との接続。 -/
lemma multiSConstructionFunctor_obj (r : ℕ) (X : StableModel.{u}) :
    (multiSConstructionFunctor r).obj X = multiSConstruction r X := rfl

/-- 概要：多単体的 core S は安定な入力について関手的。
方針：多単体的反復 S の関手を core 関手で後合成する。
規約：core は α2 の既存の関手。使われ方：実現前の自然性。 -/
def multiCoreSConstructionFunctor (r : ℕ) :
    StableModel.{u} ⥤ ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) :=
  multiSConstructionFunctor r ⋙ (Functor.whiskeringRight _ _ _).obj _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：多単体的 core の関手の各入力での値は既存の多単体的 core。
方針：後合成の定義を使う。
規約：厳密な等号。使われ方：各段の Kan 性との接続。 -/
lemma multiCoreSConstructionFunctor_obj (r : ℕ) (X : StableModel.{u}) :
    (multiCoreSConstructionFunctor r).obj X = multiCoreSConstruction r X := rfl

/-- 概要：一つの単体次数を全 S 方向へ対角に入れる関手。
方針：対象と射を各方向で同じ値にする。
規約：r = 0 も含む。使われ方：多単体構造の対角実現。 -/
def multiIndexDiagonal (r : ℕ) : SimplexCategoryᵒᵖ ⥤ (Fin r → SimplexCategoryᵒᵖ) where
  obj n := fun _ => n
  map f := fun _ => f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：多単体的単体集合から対角の単体集合を取る関手。
方針：全 S 方向を対角に制限した後で、内部の単体方向も対角に制限する。
規約：幾何実現の単体集合模型。使われ方：反復 S の各実現空間。 -/
def multiDiagonalFunctor (r : ℕ) :
    ((Fin r → SimplexCategoryᵒᵖ) ⥤ SSet.{u}) ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj (multiIndexDiagonal r) ⋙ Functor.uncurry ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategoryᵒᵖ)

/-- 概要：反復 core S の対角実現は安定な入力について関手的。
方針：多単体的 core の関手と対角の関手を合成する。
規約：Kan 置換は別工程。使われ方：連結 K スペクトルの自然性。 -/
def multiRealizationFunctor (r : ℕ) : StableModel.{u} ⥤ SSet.{u} :=
  multiCoreSConstructionFunctor r ⋙ multiDiagonalFunctor r

/-- 概要：安定な入力の反復 core S の対角実現。
方針：実現関手を入力で評価する。
規約：r 個の S 方向と内部単体方向を同時に対角に取る。
使われ方：反復 K 理論の空間。 -/
def multiDiagonalCoreSConstruction (r : ℕ) (X : StableModel.{u}) : SSet.{u} :=
  (multiRealizationFunctor r).obj X

/-- 概要：対角実現の n 単体は全 S 次数を n にした core の n 単体。
方針：対角と uncurry の対象での定義を計算する。
規約：全方向の順序は既存の有限反復と同じ。使われ方：基点と境界の記述。 -/
lemma multiDiagonalCoreSConstruction_obj (r : ℕ) (X : StableModel.{u}) (n : SimplexCategoryᵒᵖ) :
    (multiDiagonalCoreSConstruction r X).obj n =
      ((multiCoreSConstruction r X).obj (fun _ => n)).obj n := rfl

end SerrePositivity.KST.SConstruction
