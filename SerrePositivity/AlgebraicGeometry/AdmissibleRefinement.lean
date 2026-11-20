module

public import SerrePositivity.AlgebraicGeometry.SchemeProductBlowup
public import SerrePositivity.AlgebraicGeometry.Flattening

/-!
概要：KST §5、Stacks 080Y の同一基底上の admissible blowup の共通支配。
方針：積中心の二つの比較射を使い、中心外条件を支持の和で確認する。
規約：異なる基底上の blowup の合成の支配とは区別する。
使われ方：有限個の局所的な平坦化中心を同じ基底上で共通細分する準備。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {S : Scheme.{u}} (U : S.Opens) (I J : S.IdealSheafData)

/--
概要：積中心の補開集合は両中心の補開集合の共通部分。
方針：積イデアル層の支持が二つの支持の和であることを使う。
規約：KST §5、Stacks 080Y、中心の被約化は行わない。
使われ方：積中心の admissible 条件の判定。
-/
@[simp] theorem centerComplement_mul :
    centerComplement (I * J) = centerComplement I ⊓ centerComplement J := by
  ext x
  change (x ∉ (I * J).support) ↔ (x ∉ I.support ∧ x ∉ J.support)
  rw [Scheme.IdealSheafData.support_mul]
  exact not_or

/--
概要：二つの U-admissible な中心の積も U-admissible。
方針：中心の補集合の共通部分への包含を使う。
規約：KST §5、Stacks 080Y、有限生成性は不要。
使われ方：共通細分で U 上の同型を保つ。
-/
theorem isUAdmissibleCenter_mul (hI : IsUAdmissibleCenter U I)
    (hJ : IsUAdmissibleCenter U J) : IsUAdmissibleCenter U (I * J) := by
  change U ≤ centerComplement (I * J)
  rw [centerComplement_mul]
  exact le_inf hI hJ

/--
概要：アフィン局所有限生成な二中心の積もアフィン局所有限生成。
方針：各アフィン切断環で有限生成イデアルの積の有限生成性を使う。
規約：KST §5、Stacks 080Y、基底全体の Noether 性を仮定しない。
使われ方：共通細分の blowup の固有性。
-/
theorem productCenter_finiteGeneration
    (hI : ∀ V : S.affineOpens, (I.ideal V).FG)
    (hJ : ∀ V : S.affineOpens, (J.ideal V).FG) :
    ∀ V : S.affineOpens, ((I * J).ideal V).FG := by
  intro V
  exact (hI V).mul (hJ V)

/--
概要：二つの有限生成な U-admissible 中心の blowup は、一つの同種の blowup で共通支配される。
方針：積中心と両因子への実際の比較射を取る。
規約：KST §5、Stacks 080Y、支配は基底上の因子化を意味する。
使われ方：同じ基底上の有限個の中心の共通細分。
-/
theorem exists_admissible_binary_refinement
    (hI : IsUAdmissibleCenter U I) (hJ : IsUAdmissibleCenter U J)
    (hIfg : ∀ V : S.affineOpens, (I.ideal V).FG)
    (hJfg : ∀ V : S.affineOpens, (J.ideal V).FG) :
    ∃ K : S.IdealSheafData, IsUAdmissibleCenter U K ∧
      (∀ V : S.affineOpens, (K.ideal V).FG) ∧
      (∃ g : blowup K ⟶ blowup I, g ≫ blowupπ I = blowupπ K) ∧
      (∃ g : blowup K ⟶ blowup J, g ≫ blowupπ J = blowupπ K) := by
  exact ⟨I * J, isUAdmissibleCenter_mul U I J hI hJ,
    productCenter_finiteGeneration I J hIfg hJfg,
    ⟨blowupProductLeftMap I J, blowupProductLeftMap_base I J⟩,
    ⟨blowupProductRightMap I J, blowupProductRightMap_base I J⟩⟩

/--
概要：局所 Noether 基底上の有限個の U-admissible 中心の blowup は一つで共通支配される。
方針：リストの長さに関する帰納法と積中心の二つの比較射を使う。
規約：KST §5、Stacks 080Y、空族には閉補集合の消滅イデアルを使う。
使われ方：同じ基底上で有限個の平坦化中心を共通細分する。
-/
theorem exists_admissible_finite_refinement [IsLocallyNoetherian S]
    (L : List S.IdealSheafData)
    (hL : ∀ J ∈ L, IsUAdmissibleCenter U J) :
    ∃ K : S.IdealSheafData, IsUAdmissibleCenter U K ∧
      (∀ V : S.affineOpens, (K.ideal V).FG) ∧
      ∀ J ∈ L, ∃ g : blowup K ⟶ blowup J, g ≫ blowupπ J = blowupπ K := by
  induction L with
  | nil =>
    exact ⟨initialAdmissibleCenter U, initialAdmissibleCenter_admissible U,
      initialAdmissibleCenter_fg U, by simp⟩
  | cons J L ih =>
    obtain ⟨K, hKU, hKfg, hK⟩ := ih (fun A hA => hL A (List.mem_cons_of_mem J hA))
    refine ⟨J * K, isUAdmissibleCenter_mul U J K (hL J (List.mem_cons_self)) hKU,
      productCenter_finiteGeneration J K ?_ hKfg, ?_⟩
    · intro V
      have := IsLocallyNoetherian.component_noetherian V
      exact Ideal.fg_of_isNoetherianRing _
    · intro A hA
      rcases List.mem_cons.mp hA with hA | hA
      · subst A
        exact ⟨blowupProductLeftMap J K, blowupProductLeftMap_base J K⟩
      · obtain ⟨g, hg⟩ := hK A hA
        exact ⟨blowupProductRightMap J K ≫ g,
          by rw [Category.assoc, hg, blowupProductRightMap_base]⟩

/--
概要：有限個の U-admissible 中心を、中心外がちょうど U である一つの中心で共通支配する。
方針：有限族の共通細分へ U の閉補集合の消滅イデアルをさらに掛ける。
規約：KST §5、Stacks 080Y、基底は局所 Noether とする。
使われ方：大域貼り合わせで U をスキーム論的に稠密な検出開集合にする。
-/
theorem exists_admissible_family_refinement [IsLocallyNoetherian S]
    {ι : Type v} [Finite ι] (J : ι → S.IdealSheafData)
    (hJ : ∀ i, IsUAdmissibleCenter U (J i)) :
    ∃ M : S.IdealSheafData, centerComplement M = U ∧
      (∀ V : S.affineOpens, (M.ideal V).FG) ∧
      ∀ i, ∃ g : blowup M ⟶ blowup (J i), g ≫ blowupπ (J i) = blowupπ M := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let L := Finset.univ.toList.map J
  have hL : ∀ A ∈ L, IsUAdmissibleCenter U A := by
    intro A hA
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hA
    exact hJ i
  obtain ⟨K, hKU, hKfg, hK⟩ := exists_admissible_finite_refinement U L hL
  let B := initialAdmissibleCenter U
  refine ⟨B * K, ?_, productCenter_finiteGeneration B K (initialAdmissibleCenter_fg U) hKfg,
    fun i => ?_⟩
  · rw [centerComplement_mul, initialAdmissibleCenter_complement]
    exact inf_eq_left.mpr hKU
  · have hi : J i ∈ L := List.mem_map.mpr ⟨i, by simp, rfl⟩
    obtain ⟨g, hg⟩ := hK (J i) hi
    exact ⟨blowupProductRightMap B K ≫ g,
      by rw [Category.assoc, hg, blowupProductRightMap_base]⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
