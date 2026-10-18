module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.Core.ContractibleKan
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj

/-!
概要：left anodyne な射と単射の pushout-product、および相対内部 Hom の境界持ち上げ。
方針：左ホーンの積の pairing、対称性、二変数随伴を順に使う。
規約：trivial Kan fibration は全境界の持ち上げ性だけを意味する。
使われ方：Kerodon §4.2.5、§5.3.1、strict transport の始対象での評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単射と left fibration の相対内部 Hom は left fibration。
方針：左ホーンの持ち上げを対称な pushout-product の持ち上げへ移す。
規約：元の四つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §5.3.1、相対関手単体集合の制限の充填性。 -/
lemma leftFibration_pullbackObjObjπ {A D E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [LeftFibration p]
    (sq' : internalHom.PullbackObjObj i p) : LeftFibration sq'.π where
  mem := by
    intro K L j hj
    cases hj with
    | @intro n k hk =>
      obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hk)
      let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
        (curriedTensor SSet.{u}) i (horn (n + 1) k.castSucc).ι
      rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
      rw [HasLiftingProperty.iff_of_arrow_iso_left
        (show Arrow.mk sq.ι ≅ Arrow.mk sq.flipTensor.ι from
          Arrow.isoMk (Iso.refl _) (β_ _ _))]
      exact leftAnodyneExtensions_pushoutObjObj_horn k i sq.flipTensor p
        (LeftFibration.mem (p := p))

/-- 概要：単射と left anodyne な射の pushout-product は left anodyne。
方針：相対内部 Hom が left fibration であることを二変数随伴で移す。
規約：第一因子の単射性、第二因子の left anodyne 性を仮定する。
使われ方：Kerodon §4.2.5、§5.3.1、相対関手空間の制限。 -/
lemma leftAnodyneExtensions_pushoutObjObj_right {A D K L : SSet.{u}}
    (i : D ⟶ A) [Mono i] (j : K ⟶ L) (hj : leftAnodyneExtensions j)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    leftAnodyneExtensions sq.ι := by
  intro E B p hp
  have : LeftFibration p := ⟨hp⟩
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact hj sq'.π (leftFibration_pullbackObjObjπ i p sq').mem

/-- 概要：left anodyne な射と単射の pushout-product は left anodyne。
方針：因子の交換により第二因子が left anodyne な場合へ帰着する。
規約：第一因子の単射性を別に要求しない。
使われ方：Kerodon §4.2.5、§5.3.1、固定した境界の相対持ち上げ。 -/
lemma leftAnodyneExtensions_pushoutObjObj_left {A D K L : SSet.{u}}
    (i : D ⟶ A) (hi : leftAnodyneExtensions i) (j : K ⟶ L) [Mono j]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    leftAnodyneExtensions sq.ι := by
  refine (leftAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (leftAnodyneExtensions_pushoutObjObj_right j i hi sq.flipTensor)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

/-- 概要：left anodyne な制限と left fibration の相対内部 Hom は全境界を持ち上げる。
方針：境界との pushout-product の left anodyne 性を二変数随伴で移す。
規約：モデル構造を用いず全境界の持ち上げだけを主張する。
使われ方：Kerodon §5.3.1、始対象の評価の trivial Kan fibration 性。 -/
lemma trivialKanFibration_relativeHom_of_leftAnodyne {A D E B : SSet.{u}}
    (i : D ⟶ A) (hi : leftAnodyneExtensions i) (p : E ⟶ B) [LeftFibration p]
    (sq' : internalHom.PullbackObjObj i p) : TrivialKanFibration sq'.π := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) i (boundary n).ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact leftAnodyneExtensions_pushoutObjObj_left i hi (boundary n).ι sq p
    (LeftFibration.mem (p := p))

end SerrePositivity.InfinityCategories
