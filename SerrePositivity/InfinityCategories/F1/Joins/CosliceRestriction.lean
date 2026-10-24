module

public import SerrePositivity.InfinityCategories.Core.SliceUnderRestriction

public import SerrePositivity.InfinityCategories.F1.Diagrams.SquareComparison
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRightAnodyne

/-!
概要：任意の図式の射に沿う相対 coslice 制限とその合成。
方針：制限と後合成の四角形を比較写像の一般論に結び付ける。
規約：図式の射は部分複体の包含に限らない。
使われ方：Kerodon Proposition 5.1.1.14、Proposition 5.2.5.1 の三角形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：図式の制限と標的への後合成の可換四角形。
方針：coslice の前合成と後合成の可換性を使う。
規約：左の縦射が標的への後合成。
使われ方：Kerodon Proposition 5.1.1.14、相対 coslice 制限の一般形。 -/
lemma cosliceRestrictionSquare {K L X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (f : L ⟶ K) :
    CommSq (sliceUnderRestrict p f) (sliceUnderPostcomp p q)
      (sliceUnderPostcomp (f ≫ p) q) (sliceUnderRestrict (p ≫ q) f) :=
  ⟨(sliceUnderRestrict_postcomp p f q).symm⟩

/-- 概要：任意の図式の射に沿う相対 coslice 制限。
方針：制限と後合成の四角形の比較写像を取る。
規約：標的の引き戻しの第一成分は部分図式の錐。
使われ方：Kerodon Proposition 5.1.1.14、Proposition 5.2.5.1 の合成と消去。 -/
noncomputable def relativeCosliceRestriction {K L X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) :
    sliceUnder p ⟶ pullback (sliceUnderPostcomp (f ≫ p) q)
      (sliceUnderRestrict (p ≫ q) f) :=
  squareComparison (cosliceRestrictionSquare p q f)

/-- 概要：部分複体に沿う一般化した相対制限は既存の相対 coslice 射と一致。
方針：比較写像の定義を展開する。
規約：Core の定義をそのまま利用する。
使われ方：Kerodon Proposition 5.1.1.14、cocartesian 辺の判定との接続。 -/
lemma relativeCosliceRestriction_subcomplex {K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) :
    relativeCosliceRestriction p q K₀.ι = relativeCosliceMap p q K₀ := rfl

/-- 概要：二つの相対 coslice 制限が trivial Kan fibration なら合成もそうなる。
方針：比較写像の横合成則と制限の合成則を使う。
規約：図式の射 f、g の順に制限する。
使われ方：Kerodon Proposition 5.2.5.1、三角形から始点への相対制限。 -/
lemma relativeCosliceRestriction_trivialKanFibration_comp {K L M X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) (g : M ⟶ L)
    [TrivialKanFibration (relativeCosliceRestriction p q f)]
    [TrivialKanFibration (relativeCosliceRestriction (f ≫ p) q g)] :
    TrivialKanFibration (relativeCosliceRestriction p q (g ≫ f)) := by
  have : TrivialKanFibration (squareComparison (cosliceRestrictionSquare p q f)) :=
    (inferInstance : TrivialKanFibration (relativeCosliceRestriction p q f))
  have : TrivialKanFibration (squareComparison (cosliceRestrictionSquare (f ≫ p) q g)) :=
    (inferInstance : TrivialKanFibration (relativeCosliceRestriction (f ≫ p) q g))
  have h := squareComparison_trivialKanFibration_horiz_comp
    (cosliceRestrictionSquare p q f) (cosliceRestrictionSquare (f ≫ p) q g)
  exact (squareComparison_trivialKanFibration_congr _
    (cosliceRestrictionSquare p q (g ≫ f))
    (sliceUnderRestrict_comp p f g) (sliceUnderRestrict_comp (p ≫ q) f g)).mp h

/-- 概要：相対 coslice 制限の合成から後半の trivial Kan fibration 性を消去で得る。
方針：前半の相対比較と底の制限の充填を使う。
規約：底の f に沿う制限にも trivial Kan fibration 性を仮定する。
使われ方：Kerodon Proposition 5.2.5.1、三角形の長辺の cocartesian 性の判定。 -/
lemma relativeCosliceRestriction_trivialKanFibration_cancel {K L M X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K) (g : M ⟶ L)
    [TrivialKanFibration (sliceUnderRestrict (p ≫ q) f)]
    [TrivialKanFibration (relativeCosliceRestriction p q f)]
    [TrivialKanFibration (relativeCosliceRestriction p q (g ≫ f))] :
    TrivialKanFibration (relativeCosliceRestriction (f ≫ p) q g) := by
  have : TrivialKanFibration (squareComparison (cosliceRestrictionSquare p q f)) :=
    (inferInstance : TrivialKanFibration (relativeCosliceRestriction p q f))
  have : TrivialKanFibration (squareComparison
      ((cosliceRestrictionSquare p q f).horiz_comp
        (cosliceRestrictionSquare (f ≫ p) q g))) := by
    exact (squareComparison_trivialKanFibration_congr _
      (cosliceRestrictionSquare p q (g ≫ f))
      (sliceUnderRestrict_comp p f g) (sliceUnderRestrict_comp (p ≫ q) f g)).mpr
        (inferInstance : TrivialKanFibration (relativeCosliceRestriction p q (g ≫ f)))
  exact squareComparison_trivialKanFibration_cancel_left
    (cosliceRestrictionSquare p q f) (cosliceRestrictionSquare (f ≫ p) q g)

end SerrePositivity.InfinityCategories
