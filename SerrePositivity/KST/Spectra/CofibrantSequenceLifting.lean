module

public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping

/-!
概要：単射な構造射を持つ Kan 列からの厳密な持ち上げ。
方針：零段では基点包含を、次の段では構造射を左辺として相対充填する。
規約：右射には各段で全ての単射への RLP を要求する。Ω 条件は使わない。
使われ方：BF 1978 §2、HTT A.3.3。mapping path の単射置換後の厳密な因子分解。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単射を左辺とする点つき可換正方形は点つきの持ち上げを持つ。
方針：基礎単体集合で充填し、左辺が基点を含むことから基点条件を回収する。
規約：右辺の全ての単射への RLP を明示する。
使われ方：BF 1978 §2、HTT A.3.3。次の段の射の帰納構成。 -/
def pointedSquareLift {A B E Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) [Mono i.right] (q : E ⟶ Z)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q.right)
    (a : A ⟶ E) (b : B ⟶ Z) (h : a ≫ q = i ≫ b) :
    { l : B ⟶ E // i ≫ l = a ∧ l ≫ q = b } := by
  let : HasLiftingProperty i.right q.right := hq i.right inferInstance
  let sq : CommSq a.right i.right q.right b.right := ⟨congrArg Under.Hom.right h⟩
  let l : B ⟶ E := Under.homMk sq.lift (by
    rw [← Under.w i, Category.assoc, sq.fac_left, Under.w a])
  exact ⟨l, Under.UnderMorphism.ext sq.fac_left, Under.UnderMorphism.ext sq.fac_right⟩

/-- 概要：全単射に RLP を持つ点つき射へ、任意の点つき射を持ち上げる。
方針：源の基点包含を左辺として充填する。
規約：点つき射を選ぶために選択公理を使う。
使われ方：BF 1978 §2、HTT A.3.3。零段の持ち上げ。 -/
def pointedMapLift {B E Z : PointedSimplicialSet.{u}} (q : E ⟶ Z)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q.right) (b : B ⟶ Z) :
    { l : B ⟶ E // l ≫ q = b } := by
  let : Mono B.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono B
  let : HasLiftingProperty B.hom q.right := hq B.hom inferInstance
  let sq : CommSq E.hom B.hom q.right b.right := ⟨by rw [Under.w q, Under.w b]⟩
  exact ⟨Under.homMk sq.lift sq.fac_left, Under.UnderMorphism.ext sq.fac_right⟩

namespace KanSequence

variable {X W Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom W Z) (hq : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (q.app n).right)
  (f : Hom X Z)

/-- 概要：一つの段の持ち上げから、構造射と可換な次段の持ち上げを選ぶ。
方針：源の単射な構造射を左辺として点つき正方形を充填する。
規約：入力の比較式は前段だけで、出力の比較式は次段と構造射の両方。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの射の帰納構成。 -/
def liftNext (n : ℕ)
    (s : { g : (X.level n).space ⟶ (W.level n).space // g ≫ q.app n = f.app n }) :
    { t : { g : (X.level (n + 1)).space ⟶ (W.level (n + 1)).space //
        g ≫ q.app (n + 1) = f.app (n + 1) } //
      X.sigma n ≫ t.val = PointedSimplicialSet.circle.{u} ◁ s.val ≫ W.sigma n } := by
  let : Mono (X.sigma n).right := hX n
  have h : (PointedSimplicialSet.circle.{u} ◁ s.val ≫ W.sigma n) ≫ q.app (n + 1) =
      X.sigma n ≫ f.app (n + 1) := by
    rw [Category.assoc, ← q.comm n, ← Category.assoc,
      ← whiskerLeft_comp, s.property, f.comm n]
  let l := pointedSquareLift (X.sigma n) (q.app (n + 1)) (hq (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ s.val ≫ W.sigma n) (f.app (n + 1)) h
  exact ⟨⟨l.val, l.property.2⟩, l.property.1⟩

/-- 概要：持ち上げを自然数の段に沿って選ぶ。
方針：零段の基点充填から始め、各後続段で相対充填を使う。
規約：各段には右射との厳密な比較式を含める。
使われ方：BF 1978 §2、HTT A.3.3。厳密な列の射の構成。 -/
def liftStage : (n : ℕ) →
    { g : (X.level n).space ⟶ (W.level n).space // g ≫ q.app n = f.app n }
  | 0 => pointedMapLift (q.app 0) (hq 0) (f.app 0)
  | n + 1 => (liftNext hX q hq f n (liftStage n)).val

/-- 概要：cofibrant な源から全単射への段ごとの RLP を持つ射への厳密な持ち上げ。
方針：帰納構成した段を束ね、次段の相対条件を構造射の可換式に使う。
規約：Ω 条件やモデル構造の弱同値を仮定しない。
使われ方：BF 1978 §2、HTT A.3.3。任意の射の fibration 置換。 -/
def liftHom : Hom X W where
  app n := (liftStage hX q hq f n).val
  comm n := (liftNext hX q hq f n (liftStage hX q hq f n)).property.symm

/-- 概要：選んだ列の持ち上げを右射へ合成すると元の射。
方針：各段の比較式を取り出す。
規約：段ごとの厳密な等式。
使われ方：BF 1978 §2。mapping path の厳密な因子分解の比較。 -/
theorem liftHom_fac (n : ℕ) : (liftHom hX q hq f).app n ≫ q.app n = f.app n :=
  (liftStage hX q hq f n).property

end KanSequence

end

end SerrePositivity.KST.Spectra
