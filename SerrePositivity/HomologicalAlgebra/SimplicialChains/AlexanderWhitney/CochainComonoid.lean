module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCoassociativity
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounitLaws
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 正規化鎖の整数コチェイン模型の余代数関手

概要：既存 AW 対角と余単位を Mathlib の Comon に束ねる。
方針：既存の三律と自然性を使い、通常の正規化関手を持ち上げる。
規約：cochains は正規化鎖の負次数配置なので単体集合に共変。双対化しない。
使われ方：Sp の K-9 β6 f4 へ標準単体の余代数を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.SimplicialChains.AlexanderWhitney
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：既存の複体の AW 余代数構造。
方針：余単位則を単位子の逆の式へ直し、余結合則を使う。
規約：大域 instance にせず既存の対角・余単位を保つ。
使われ方：cochainComon の構造欄。 -/
@[instance_reducible]
def cochainComonObj (X : SSet.{0}) : ComonObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X) where
  counit := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X
  comul := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X
  counit_comul := by
    change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
      HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X) (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) =
        (HomologicalComplex.leftUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).inv
    apply (cancel_mono (HomologicalComplex.leftUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id] using _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_left_counit A X
  comul_counit := by
    change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X ≫
      HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X) =
        (HomologicalComplex.rightUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).inv
    apply (cancel_mono (HomologicalComplex.rightUnitor (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X)).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id] using _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_right_counit A X
  comul_assoc := (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_coassoc A X).symm

/-- 概要：任意の小さい単体集合の束ねた余代数。
方針：既存 cochains と AW 構造を組にする。規約：係数環は任意の可換環。
使われ方：余代数関手の対象写像。 -/
def cochainComon (X : SSet.{0}) : Comon (Complex A) where
  X := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X
  comon := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonObj A X

/-- 概要：単体集合の射が誘導する共変な余代数射。
方針：既存の対角・余単位の自然性を使う。規約：底の射は cochainMap 自身。
使われ方：余代数関手の射写像。 -/
def cochainComonMap {X Y : SSet.{0}} (f : X ⟶ Y) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A X ⟶ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A Y :=
  Comon.Hom.mk' (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural A f) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_natural A f)

/-- 概要：束ねた対象の底は既存の cochains。
方針：定義を読む。規約：定義上の一致。使われ方：Sp の既存複体との照合。 -/
@[simp] lemma cochainComon_X (X : SSet.{0}) : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A X).X = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A X := rfl

/-- 概要：束ねた余乗法は既存の AW 対角。
方針：構造欄を読む。規約：定義上の一致。使われ方：底の対角との照合。 -/
@[simp] lemma cochainComon_comul (X : SSet.{0}) :
    @ComonObj.comul _ _ _ _ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A X).comon = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal A X := rfl

/-- 概要：束ねた余単位は既存の augmentation。
方針：構造欄を読む。規約：定義上の一致。使われ方：底の余単位との照合。 -/
@[simp] lemma cochainComon_counit (X : SSet.{0}) :
    @ComonObj.counit _ _ _ _ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A X).comon = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A X := rfl

/-- 概要：束ねた射の底は既存の cochainMap。
方針：射の定義を読む。規約：向きも定義上同じ。使われ方：元の正規化射との照合。 -/
@[simp] lemma cochainComonMap_hom {X Y : SSet.{0}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A f).hom = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f := rfl

/-- 概要：束ねた射は恒等射を保つ。
方針：底の正規化関手の律を使う。規約：余代数射の等式。使われ方：関手性。 -/
@[simp] lemma cochainComonMap_id (X : SSet.{0}) : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A (𝟙 X) = 𝟙 _ := by
  apply Comon.ext
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map_id X

/-- 概要：束ねた射は合成を保つ。
方針：底の正規化関手の律を使う。規約：共変の合成順序。使われ方：関手性。 -/
@[simp] lemma cochainComonMap_comp {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A (f ≫ g) = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A g := by
  apply Comon.ext
  exact (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map_comp f g

/-- 概要：小さい単体集合から複体の余代数への共変関手。
方針：既存正規化関手の対象と射を束ねる。規約：反変化・双対化は行わない。
使われ方：標準単体への制限と任意の単体集合の AW 構造。 -/
def cochainComonFunctor : SSet.{0} ⥤ Comon (Complex A) where
  obj := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon A
  map := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap A
  map_id := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap_id A
  map_comp := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonMap_comp A

/-- 概要：余代数関手を忘れると元の正規化関手。
方針：対象と射の定義を読む。規約：全関手の定義上の一致。
使われ方：既存の cochains の全自然性との照合。 -/
@[simp] lemma cochainComonFunctor_forget :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor A ⋙ Comon.forget (Complex A) = _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A := rfl

/-- 概要：標準単体の余代数の余単体的関手。
方針：標準単体関手と cochainComonFunctor を合成する。
規約：SimplexCategory に共変。使われ方：Sp の K-9 β6 f4。 -/
def simplexCochainComonFunctor : SimplexCategory ⥤ Comon (Complex A) :=
  stdSimplex ⋙ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor A

/-- 概要：標準単体の束ねた対象の底を照合する。
方針：合成関手の定義を読む。規約：定義上の一致。使われ方：Δ[n] の複体の回収。 -/
@[simp] lemma simplexCochainComonFunctor_obj_X (n : SimplexCategory) :
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor A).obj n).X = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (stdSimplex.obj n) := rfl

/-- 概要：標準単体の射の底を照合する。
方針：合成関手の定義を読む。規約：定義上の一致。使われ方：面・退化射との接続。 -/
@[simp] lemma simplexCochainComonFunctor_map_hom {m n : SimplexCategory} (f : m ⟶ n) :
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor A).map f).hom = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (stdSimplex.map f) := rfl

/-- 概要：標準単体の余代数関手を忘れた全関手の照合。
方針：対象と射の定義を読む。規約：定義上の一致。
使われ方：Sp の既存の標準単体複体への接続。 -/
@[simp] lemma simplexCochainComonFunctor_forget :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor A ⋙ Comon.forget (Complex A) =
      SSet.stdSimplex ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A := rfl

end SerrePositivity.SimplicialChains.AlexanderWhitney
