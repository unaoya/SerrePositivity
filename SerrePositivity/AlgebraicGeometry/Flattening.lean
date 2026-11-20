module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupProper
public import SerrePositivity.AlgebraicGeometry.SchemeExceptional
public import SerrePositivity.AlgebraicGeometry.BlowupDensity

/-!
概要：Stacks 081T の Noether 特殊形による blowup 支配のための古典的基盤。
方針：U を避ける実際の中心とその blowup を構成し、strict transform の平坦化へ進む。
規約：未証明の平坦化・支配を公理や構造体のフィールドに置かない。
使われ方：KST §5.2、Temkin 2008 Lemma 2.1.5 の幾何学的入力。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {S : Scheme.{u}}

/--
概要：中心の支持が開集合 U を避けるという admissible 条件。
方針：中心の補開集合が U を含むという包含で表す。
規約：Stacks 081T、KST §5.2、Temkin 2008 Lemma 2.1.5。
使われ方：実際の blowup が U 上で同型であることを導く。
-/
def IsUAdmissibleCenter (U : S.Opens) (J : S.IdealSheafData) : Prop :=
  U ≤ centerComplement J

set_option backward.isDefEq.respectTransparency false in
/--
概要：U-admissible な中心の実際の blowup は U 上で同型。
方針：中心外同型を U にさらに制限して一回の制限に同定する。
規約：Stacks 081T、未証明の支配の存在は仮定しない。
使われ方：admissible blowup による変形で U 上のデータを保持する。
-/
theorem blowupπ_restrict_admissible_isIso (U : S.Opens) (J : S.IdealSheafData)
    (hJ : IsUAdmissibleCenter U J) : IsIso (blowupπ J ∣_ U) := by
  let C := centerComplement J
  let V := C.ι ⁻¹ᵁ U
  have := blowupπ_restrict_complement_isIso J
  have h : IsIso ((blowupπ J ∣_ C) ∣_ V) := inferInstance
  change (MorphismProperty.isomorphisms Scheme) ((blowupπ J ∣_ C) ∣_ V) at h
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (blowupπ J) C V)] at h
  have heq : C.ι ''ᵁ V = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hJ
  change IsIso (blowupπ J ∣_ C.ι ''ᵁ V) at h
  rw [heq] at h
  exact h

/--
概要：正の冪を取っても U-admissible な中心という条件は変わらない。
方針：イデアル層の正の冪の支持が元の支持に一致することを使う。
規約：Stacks 081T、冪指数は正。
使われ方：中心の厚みを変えて blowup を比較する。
-/
theorem isUAdmissibleCenter_pow (U : S.Opens) (J : S.IdealSheafData)
    (n : ℕ) (hn : 0 < n) :
    IsUAdmissibleCenter U (J ^ n) ↔ IsUAdmissibleCenter U J := by
  simp only [IsUAdmissibleCenter, centerComplement, J.support_pow n hn.ne']

/--
概要：開集合の閉補集合を中心とする消滅イデアル層。
方針：閉集合の実際の消滅イデアル層を取る。
規約：Stacks 080Y Remark 38.30.1、081T の最初の Cartier 化の中心。
使われ方：U を避け、その補集合全体を支持に持つ blowup の構成。
-/
def initialAdmissibleCenter (U : S.Opens) : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal U.compl

/--
概要：最初の admissible 中心の支持は U の閉補集合。
方針：消滅イデアル層の支持の定義を使う。
規約：Stacks 080Y Remark 38.30.1、中心を被約な閉集合の消滅イデアルで固定する。
使われ方：最初の blowup の中心外開集合を U と同定する。
-/
@[simp] theorem initialAdmissibleCenter_support (U : S.Opens) :
    (initialAdmissibleCenter U).support = U.compl := rfl

/--
概要：最初の admissible 中心の補開集合は U そのもの。
方針：支持の同定と補集合の二重化を用いる。
規約：Stacks 081T、任意の基礎スキームで成立する。
使われ方：U 上の同型と補集合の Cartier 化。
-/
@[simp] theorem initialAdmissibleCenter_complement (U : S.Opens) :
    centerComplement (initialAdmissibleCenter U) = U := by
  simp only [centerComplement, initialAdmissibleCenter_support, TopologicalSpace.Opens.compl_compl]

/--
概要：開集合の閉補集合の消滅イデアルは U-admissible な中心。
方針：中心の補集合が U に等しいことを使う。
規約：Stacks 081T、存在定理を仮定せず実際の中心を構成する。
使われ方：最初の admissible blowup。
-/
theorem initialAdmissibleCenter_admissible (U : S.Opens) :
    IsUAdmissibleCenter U (initialAdmissibleCenter U) := by
  unfold IsUAdmissibleCenter
  rw [initialAdmissibleCenter_complement]

/--
概要：Noether 基底の開集合は準コンパクト。
方針：Noether 位相空間の全ての部分集合のコンパクト性を使う。
規約：Stacks 081T の準コンパクトな開集合という仮定を Noether 性から導く。
使われ方：平坦化の有限被覆の選択。
-/
theorem noetherian_open_isCompact [_root_.AlgebraicGeometry.IsNoetherian S] (U : S.Opens) :
    IsCompact (U : Set S) := TopologicalSpace.NoetherianSpace.isCompact _

/--
概要：局所 Noether 基底で最初の admissible 中心は全アフィン上で有限生成。
方針：切断環の Noether 性を用いる。
規約：Stacks 081T の Noether 特殊形、有限型中心を追加仮定しない。
使われ方：最初の blowup の固有性。
-/
theorem initialAdmissibleCenter_fg [IsLocallyNoetherian S] (U : S.Opens)
    (V : S.affineOpens) : ((initialAdmissibleCenter U).ideal V).FG := by
  have := IsLocallyNoetherian.component_noetherian V
  exact Ideal.fg_of_isNoetherianRing _

/--
概要：最初の admissible blowup では U の逆像は基底変更後の全体で稠密。
方針：中心補集合が U と一致することと、blowup の中心外稠密性を使う。
規約：Stacks 080Y Remark 38.30.1、081T。ここでは位相的稠密性を述べる。
使われ方：平坦化後の固有な開部分スキームとの同定の最後の段階。
-/
theorem initialAdmissibleBlowup_dense (U : S.Opens) :
    Dense (blowupπ (initialAdmissibleCenter U) ⁻¹ᵁ U).carrier := by
  have h := blowup_centerComplement_dense (initialAdmissibleCenter U)
  rw [initialAdmissibleCenter_complement] at h
  exact h

/--
概要：Noether 基底で U を避け、補集合を Cartier 化する最初の固有 blowup を構成する。
方針：閉補集合の消滅イデアルを中心に選び、既存の固有性・例外因子・稠密性を適用する。
規約：Stacks 080Y Remark 38.30.1、081T。平坦化による最終的な支配の存在とは区別する。
使われ方：Noether 特殊形の支配定理の最初の段階。
-/
theorem exists_initial_admissible_blowup [_root_.AlgebraicGeometry.IsNoetherian S] (U : S.Opens) :
    ∃ J : S.IdealSheafData,
      (∀ V : S.affineOpens, (J.ideal V).FG) ∧ IsUAdmissibleCenter U J ∧
      centerComplement J = U ∧ IsProper (blowupπ J) ∧
      IsEffectiveCartierImmersion (exceptionalι J) ∧ Dense (blowupπ J ⁻¹ᵁ U).carrier := by
  refine ⟨initialAdmissibleCenter U, initialAdmissibleCenter_fg U,
    initialAdmissibleCenter_admissible U, initialAdmissibleCenter_complement U,
    inferInstance, exceptional_isEffectiveCartier _, initialAdmissibleBlowup_dense U⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
