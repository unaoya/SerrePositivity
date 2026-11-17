module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：関手準圏 Fun(C,C) の合成を、全単体集合上の積として固定する。
方針：閉モノイダル構造の内部 Hom の合成を使い、単位・結合則を単体写像の等式で示す。
規約：積は左の関手の後に右の関手を適用する順序。C のホモトピー圏へは忘却しない。
使われ方：HA §4.7.2–§4.7.3、Proposition 4.7.3.3 の誘導モナドの周囲の合成。
Kerodon Remark 6.2.1.4（Tag 02EN）の h Fun への移行に先立つ全関手単体集合を使う。
このファイルは周囲の合成だけを構成し、随伴の coherent なモナドへの持ち上げは別に行う。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全自己関手の単体集合。方針：閉構造の内部 Hom を取る。
規約：宇宙を変えない。使われ方：HA §4.7.2–§4.7.3 のモナドの周囲。 -/
abbrev EndofunctorSpace (C : SSet.{u}) : SSet.{u} := (ihom C).obj C

/-- 概要：準圏の全自己関手は準圏をなす。
方針：内部 Hom の inner horn 充填を使う。規約：C 自身の準圏性だけを仮定する。
使われ方：HA Proposition 4.7.3.3 の自己関手準圏。 -/
instance endofunctorSpace_quasicategory (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (EndofunctorSpace C) := inferInstanceAs (Quasicategory ((ihom C).obj C))

/-- 概要：恒等自己関手を全合成の単位として指定する。
方針：恒等写像の curry を取る。規約：単体集合のテンソル単位からの射。
使われ方：HA §4.7.2–§4.7.3 の単位。 -/
def endofunctorUnit (C : SSet.{u}) : 𝟙_ SSet ⟶ EndofunctorSpace C :=
  MonoidalClosed.id C

/-- 概要：二つの全自己関手を合成する単体写像。
方針：内部 Hom の豊穣合成。規約：第一因子の後に第二因子を適用する。
使われ方：HA Proposition 4.7.3.3 の積の周囲。 -/
def endofunctorComposition (C : SSet.{u}) :
    EndofunctorSpace C ⊗ EndofunctorSpace C ⟶ EndofunctorSpace C :=
  MonoidalClosed.comp C C C

/-- 概要：合成の左単位則を全単体写像として示す。
方針：内部 Hom の左単位則を使う。規約：全ての次数での等式。
使われ方：HA §4.7.2 の単位付き合成。 -/
lemma endofunctorUnit_comp (C : SSet.{u}) :
    (λ_ (EndofunctorSpace C)).inv ≫ endofunctorUnit C ▷ _ ≫
      endofunctorComposition C = 𝟙 _ :=
  MonoidalClosed.id_comp C C

/-- 概要：合成の右単位則を全単体写像として示す。
方針：内部 Hom の右単位則を使う。規約：恒等関手は第二因子。
使われ方：HA §4.7.2 の単位付き合成。 -/
lemma endofunctorComp_unit (C : SSet.{u}) :
    (ρ_ (EndofunctorSpace C)).inv ≫ _ ◁ endofunctorUnit C ≫
      endofunctorComposition C = 𝟙 _ :=
  MonoidalClosed.comp_id C C

/-- 概要：三つの全自己関手の合成の結合則。
方針：内部 Hom の豊穣結合則を使う。規約：テンソルの結合子を明記する。
使われ方：HA §4.7.2–§4.7.3 の合成の coherence。 -/
lemma endofunctorComp_assoc (C : SSet.{u}) :
    (α_ _ _ _).inv ≫ endofunctorComposition C ▷ _ ≫ endofunctorComposition C =
      _ ◁ endofunctorComposition C ≫ endofunctorComposition C :=
  MonoidalClosed.assoc C C C C

/-- 概要：全自己関手の合成を単体集合の内部モノイドにまとめる。
方針：上の全単位・結合則から実際に構成する。規約：これは周囲の合成であって、
自己関手 T 上のモナド構造ではない。使われ方：HA §4.7.2–§4.7.3。 -/
@[instance_reducible]
def endofunctorCompositionMonObj (C : SSet.{u}) : MonObj (EndofunctorSpace C) where
  one := endofunctorUnit C
  mul := endofunctorComposition C
  one_mul := by
    rw [← cancel_epi (λ_ (EndofunctorSpace C)).inv]
    simpa using endofunctorUnit_comp C
  mul_one := by
    rw [← cancel_epi (ρ_ (EndofunctorSpace C)).inv]
    simpa using endofunctorComp_unit C
  mul_assoc := by
    rw [← cancel_epi (α_ (EndofunctorSpace C) (EndofunctorSpace C)
      (EndofunctorSpace C)).inv]
    simpa using endofunctorComp_assoc C

/-- 概要：恒等関手の頂点表示が指定単位と一致する。
方針：恒等写像の curry の式を使う。規約：単位からの射として比較する。
使われ方：HA Proposition 4.7.3.3 の元の単位の照合。 -/
lemma endofunctorUnit_eq_curry (C : SSet.{u}) :
    endofunctorUnit C = curry' (𝟙 C) :=
  (MonoidalClosed.curry'_id C).symm

/-- 概要：全合成は実際の自己関手の合成を拡張する。
方針：二つの curry の豊穣合成公式を使う。規約：元の f ≫ g の順序を保つ。
使われ方：HA Proposition 4.7.3.3 の underlying endofunctor の照合。 -/
lemma endofunctorComposition_curry {C : SSet.{u}} (f g : C ⟶ C) :
    (λ_ (𝟙_ SSet)).inv ≫ (curry' f ⊗ₘ curry' g) ≫ endofunctorComposition C =
      curry' (f ≫ g) :=
  (MonoidalClosed.curry'_comp f g).symm

end SerrePositivity.InfinityCategories.HA.Monads
