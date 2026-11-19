module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.DisjointOpenCenters
public import SerrePositivity.AlgebraicGeometry.DisjointOpenCoverClosed
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback

/-!
概要：KST §5、Stacks Lemma 31.35.5・0811 の有限開閉分割上の局所中心の正確な貼り合わせ。
方針：延長中心の有限共通部分を取り、各部分への制限等式と中心補開集合を照合する。
規約：局所 Noether 基底上で実際のイデアル層とアフィン局所有限生成性を返す。
使われ方：階数を分離した有限チャート上の第二段の中心を全体へまとめる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：有限個の互いに交わらない開被覆上の中心を、各制限が元に一致する一つの有限生成中心に貼り合わせられる。
方針：各像の閉性から延長中心の別部分への逆像を単位とし、有限共通部分の制限を計算する。
規約：KST §5、Stacks Lemma 31.35.5・0811、各局所中心の補集合は指定した U の逆像とする。
使われ方：二段目の局所 blowup を、第一段の blowup 上の一つの中心から得る。
-/
theorem exists_center_of_disjoint_open_cover
    {ι : Type v} [Finite ι] {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : ι → Scheme.{u}} (j : ∀ i, X i ⟶ S)
    [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hcover : (⨆ i, (j i).opensRange) = ⊤)
    (hd : Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange))
    (U : S.Opens) (K : ∀ i, (X i).IdealSheafData)
    (hK : ∀ i, centerComplement (K i) = j i ⁻¹ᵁ U) :
    ∃ L : S.IdealSheafData, (∀ V : S.affineOpens, (L.ideal V).FG) ∧
      (∀ i, L.comap (j i) = K i) ∧ centerComplement L = U := by
  have hj (i : ι) : IsClosed (Set.range (j i)) := by
    change IsClosed ((j i).opensRange : Set S)
    exact isClosed_of_disjoint_open_cover (fun i => (j i).opensRange) hcover hd i
  have hdSet : Pairwise (fun i k => Disjoint (Set.range (j i)) (Set.range (j k))) := by
    intro i k hik
    rw [Set.disjoint_left]
    intro x hxi hxk
    exact (disjoint_iff_inf_le.mp (hd hik)) ⟨hxi, hxk⟩
  let L : S.IdealSheafData := ⨅ i, (K i).map (j i)
  have hrest (i : ι) : L.comap (j i) = K i :=
    idealSheaf_comap_iInf_map_of_disjoint_closed_images j hj hdSet K i
  refine ⟨L, ?_, hrest, ?_⟩
  · intro V
    have := IsLocallyNoetherian.component_noetherian V
    exact Ideal.fg_of_isNoetherianRing _
  · ext x
    have hx : x ∈ ⨆ i, (j i).opensRange := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    change x ∈ Set.range (j i) at hi
    obtain ⟨y, rfl⟩ := hi
    have heq : j i ⁻¹ᵁ centerComplement L = j i ⁻¹ᵁ U := by
      rw [preimage_centerComplement_comap, hrest, hK]
    change y ∈ j i ⁻¹ᵁ centerComplement L ↔ y ∈ j i ⁻¹ᵁ U
    rw [heq]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
