module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorSpace
public import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：右ホーンと単射の pushout-product、および right fibration の内部 Hom。
方針：左ホーンの積の pairing を反転し、相対内部 Hom の持ち上げへ移す。
規約：straightening やモデル構造の弱同値を用いない。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Proposition 7.2.1.3（Tag 02N3） の right 側。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：pairing core の最後以外という条件を型 II の単体へ移す。
方針：core の添字と型 II の単体の全単射で戻す。
規約：core の正則性を仮定する。
使われ方：右ホーンの積の pairing を反転する際の添字の検査。 -/
lemma cofinalPairingCore_index_ne_last {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.PairingCore) [P.pairing.IsRegular]
    (hn : ∀ s : P.ι, P.index s ≠ Fin.last (P.dim s + 1))
    (s : P.pairing.II) :
    (P.pairing.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1) := by
  have := (P.isProper_pairing_iff).1 (inferInstance : P.pairing.IsProper)
  obtain ⟨t, rfl⟩ := P.equivII.surjective s
  intro hz
  have hv := congrArg Fin.val hz
  have hj : ((P.pairing.isUniquelyCodimOneFace (P.equivII t)).index rfl).val =
      (P.index t).val := by simp
  have hd : (P.equivII t).val.dim = P.dim t := by
    change (P.type₂ t).dim = P.dim t
    rfl
  rw [hj, Fin.val_last, hd] at hv
  exact hn t (Fin.ext hv)

/-- 概要：任意の右ホーンと境界の積の和は right anodyne。
方針：左ホーンと境界の pairing を反転して標準単体の積へ戻す。
規約：k.castSucc.rev は零以外の全ての右ホーンを走る。
使われ方：right fibration の相対内部 Hom の持ち上げ。 -/
lemma cofinalRightAnodyne_unionProd {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions
      (Subcomplex.unionProd.{u} (horn (m + 1) k.castSucc.rev) (boundary n)).ι := by
  let e := ((stdSimplex.opIso ⦋m + 1⦌).symm ⊗ᵢ (stdSimplex.opIso ⦋n⦌).symm) ≪≫
    Functor.Monoidal.μIso opFunctor Δ[m + 1] Δ[n]
  have hA : (Subcomplex.unionProd.{u} (horn (m + 1) k.castSucc) (boundary n)).op.preimage e.hom =
      Subcomplex.unionProd (horn (m + 1) k.castSucc.rev) (boundary n) := by
    dsimp [e]
    rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
      Subcomplex.preimage_unionProd, op_boundary, op_horn]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pairing_rightAnodyneExtensions
    ((prodStdSimplex.pairingCore.{u} k n).pairing.op.ofIso e hA)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pairing_ofIso_index_ne_zero
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pairing_op_index_ne_zero
  apply cofinalPairingCore_index_ne_last
  intro s
  exact Fin.castSucc_ne_last s.index

/-- 概要：右ホーンと任意の単射の pushout-product は right anodyne。
方針：内部 Hom の相対射の持ち上げ性を境界で検査し、積の pairing に帰着する。
規約：右ホーンの欠ける面は零以外。
使われ方：Kerodon §4.2.5（Tag 0152）、§5.3.1（Tag 035D）、相対関手の右ホーン充填。 -/
lemma cofinalRightAnodyne_pushoutObjObj_horn {m : ℕ} (k : Fin (m + 1))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn (m + 1) k.castSucc.rev).ι i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions sq.ι := by
  intro E D p hp
  let sq' := Functor.PullbackObjObj.ofHasPullback internalHom
    (horn (m + 1) k.castSucc.rev).ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  suffices (monomorphisms SSet.{u}).rlp sq'.π from this _ inferInstance
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} (horn (m + 1) k.castSucc.rev) (boundary n)) sq',
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact cofinalRightAnodyne_unionProd k n p hp

/-- 概要：右ホーンの包含と任意の単体集合の直積は right anodyne。
方針：空の単体集合からの包含との pushout-product を使う。
規約：パラメータ A の quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、内部 Hom の right fibration 性の随伴による証明。 -/
lemma cofinalRightAnodyne_horn_whiskerRight {m : ℕ} (k : Fin (m + 1))
    (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((horn (m + 1) k.castSucc.rev).ι ▷ A) :=
  cofinalRightAnodyne_pushoutObjObj_horn k (initial.to A)
    (.ofIsInitialRight (curriedTensor _) (horn (m + 1) k.castSucc.rev).ι
      (initial.to A) initialIsInitial)

/-- 概要：right fibration による後合成は任意の内部 Hom 上で right fibration。
方針：tensorRight と内部 Hom の随伴で、右ホーンとパラメータの積の持ち上げに移す。
規約：パラメータと底に quasicategory 性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、right fibration 上の関手の族の充填。 -/
@[kerodon 00TQ]
instance cofinalIhom_map_rightFibration {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (A : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration ((ihom A).map p) where
  mem := by
    intro K L i hi
    cases hi with
    | @intro n k hk =>
      have hr : k.rev < Fin.last (n + 1) := by
        change k.rev.val < n + 1
        rw [Fin.val_rev]
        change 0 < k.val at hk
        omega
      obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hr)
      have he : j.castSucc.rev = k := by rw [hj, Fin.rev_rev]
      rw [← he]
      exact (((ihom.adjunction A).ofNatIsoLeft
        (BraidedCategory.tensorLeftIsoTensorRight A)).hasLiftingProperty_iff _ p).1
        (cofinalRightAnodyne_horn_whiskerRight j A p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p)))

/-- 概要：単射と right fibration の相対内部 Hom は right fibration。
方針：右ホーンの持ち上げを対称な pushout-product の持ち上げへ移す。
規約：元の四つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手単体集合の制限の充填性。 -/
@[kerodon 00TP]
lemma cofinalRightFibration_pullbackObjObjπ {A D E B : SSet.{u}}
    (i : D ⟶ A) [Mono i] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (sq' : internalHom.PullbackObjObj i p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration sq'.π where
  mem := by
    intro K L j hj
    cases hj with
    | @intro n k hk =>
      have hr : k.rev < Fin.last (n + 1) := by
        change k.rev.val < n + 1
        rw [Fin.val_rev]
        change 0 < k.val at hk
        omega
      obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hr)
      have he : j.castSucc.rev = k := by rw [hj, Fin.rev_rev]
      rw [← he]
      let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
        (curriedTensor SSet.{u}) i (horn (n + 1) j.castSucc.rev).ι
      rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
      rw [HasLiftingProperty.iff_of_arrow_iso_left
        (show Arrow.mk sq.ι ≅ Arrow.mk sq.flipTensor.ι from
          Arrow.isoMk (Iso.refl _) (β_ _ _))]
      exact cofinalRightAnodyne_pushoutObjObj_horn j i sq.flipTensor p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))

/-- 概要：単射と right anodyne な射の pushout-product は right anodyne。
方針：相対内部 Hom が right fibration であることを二変数随伴で移す。
規約：第一因子の単射性、第二因子の right anodyne 性を仮定する。
使われ方：Kerodon §4.2.5（Tag 0152）、§5.3.1（Tag 035D）、相対関手空間の制限。 -/
@[kerodon 0153]
lemma cofinalRightAnodyne_pushoutObjObj_right {A D K L : SSet.{u}}
    (i : D ⟶ A) [Mono i] (j : K ⟶ L) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions j)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions sq.ι := by
  intro E B p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact hj sq'.π (cofinalRightFibration_pullbackObjObjπ i p sq').mem

/-- 概要：right anodyne な射と単射の pushout-product は right anodyne。
方針：因子の交換により第二因子が right anodyne な場合へ帰着する。
規約：第一因子の単射性を別に要求しない。
使われ方：Kerodon §4.2.5（Tag 0152）、§5.3.1（Tag 035D）、固定した境界の相対持ち上げ。 -/
lemma cofinalRightAnodyne_pushoutObjObj_left {A D K L : SSet.{u}}
    (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i) (j : K ⟶ L) [Mono j]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions sq.ι := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (cofinalRightAnodyne_pushoutObjObj_right j i hi sq.flipTensor)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

/-- 概要：right anodyne な制限と right fibration の相対内部 Hom は全境界を持ち上げる。
方針：境界との pushout-product の right anodyne 性を二変数随伴で移す。
規約：モデル構造を用いず全境界の持ち上げだけを主張する。
使われ方：Kerodon §5.3.1（Tag 035D）、始対象の評価の trivial Kan fibration 性。 -/
@[kerodon 0154]
lemma cofinalTrivialKanFibration_relativeHom_of_rightAnodyne {A D E B : SSet.{u}}
    (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (sq' : internalHom.PullbackObjObj i p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq'.π := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) i (boundary n).ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact cofinalRightAnodyne_pushoutObjObj_left i hi (boundary n).ι sq p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "3.1.2.1" (partial := special) "仮定：Cartesian p と任意の K（Lean が強い：p を right fibration に限定）。結論：同じ ihom K による pK が right、従って Cartesian fibration となり一致。この場合は p と pK の全辺が Cartesian なので点ごとの iff も両辺が成立する。一般の Cartesian fibration の指数は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.cofinalIhom_map_rightFibration
