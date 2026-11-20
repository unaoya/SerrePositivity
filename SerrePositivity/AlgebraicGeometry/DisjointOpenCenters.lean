module

public import SerrePositivity.AlgebraicGeometry.OpenCenterExtension
public import SerrePositivity.AlgebraicGeometry.IdealSheafLocality

/-!
概要：KST §5、Stacks Lemma 31.35.5・0811 の互いに交わらない開部分上の中心の延長。
方針：閉じた像の外で支持が空となることと、開制限の有限共通部分の保存を使う。
規約：実際のイデアル層の等式を扱う。
使われ方：一般階数を分離した有限開閉チャート上の中心を正確に貼り合わせる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/--
概要：開埋め込みによるイデアル層の逆像は有限族の共通部分を保存する。
方針：各アフィン切断を開埋め込みの切断環同型で比較し、環イデアルの逆像の共通部分保存を使う。
規約：KST §5、Stacks Lemma 31.35.5・0811、添字集合は有限。
使われ方：延長した局所中心の共通部分を元のチャートへ制限する。
-/
theorem idealSheaf_comap_iInf_of_openImmersion {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {ι : Type v} [Finite ι] (K : ι → Y.IdealSheafData) :
    (⨅ i, K i).comap j = ⨅ i, (K i).comap j := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply, Ideal.comap_iInf]

set_option backward.isDefEq.respectTransparency false in
/--
概要：閉じた像への中心の延長は、その像と交わらない部分へ制限すると単位イデアル層となる。
方針：延長中心の支持を像の閉包で計算し、閉じた像に含まれることから逆像の支持が空と示す。
規約：KST §5、Stacks Lemma 31.35.5・0811、制限側の射は開埋め込みに限らない。
使われ方：有限開閉分割の別のチャートに延長中心が影響しないことの判定。
-/
theorem idealSheaf_comap_map_eq_top_of_disjoint_closed_image
    {X Y S : Scheme.{u}} (j : X ⟶ S) [QuasiCompact j] (k : Y ⟶ S)
    (hj : IsClosed (Set.range j)) (hd : Disjoint (Set.range j) (Set.range k))
    (K : X.IdealSheafData) : (K.map j).comap k = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff ((K.map j).comap k)).mp
  apply bot_unique
  intro y hy
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_map] at hy
  change k y ∈ closure (j '' (K.support : Set X)) at hy
  have him : j '' (K.support : Set X) ⊆ Set.range j := Set.image_subset_range _ _
  have hmem : k y ∈ Set.range j := closure_minimal him hj hy
  exact (Set.disjoint_left.mp hd) hmem ⟨y, rfl⟩

/--
概要：有限個の互いに交わらない開閉像から延長した中心の共通部分は、各部分上で元の中心に一致する。
方針：同じ部分への制限は comap_map、別の部分への制限は支持が空であることから計算する。
規約：KST §5、Stacks Lemma 31.35.5・0811、各開埋め込みは準コンパクトとする。
使われ方：第二段の局所中心を制限等式付きで一つの実際の中心に貼り合わせる。
-/
theorem idealSheaf_comap_iInf_map_of_disjoint_closed_images
    {ι : Type v} [Finite ι] {S : Scheme.{u}} {X : ι → Scheme.{u}}
    (j : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (j i)] [∀ i, QuasiCompact (j i)]
    (hj : ∀ i, IsClosed (Set.range (j i)))
    (hd : Pairwise (fun i k => Disjoint (Set.range (j i)) (Set.range (j k))))
    (K : ∀ i, (X i).IdealSheafData) (i : ι) :
    (⨅ k, (K k).map (j k)).comap (j i) = K i := by
  rw [idealSheaf_comap_iInf_of_openImmersion]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq (idealSheaf_comap_map_openImmersion (j i) (K i))
  · apply le_iInf
    intro k
    by_cases hki : k = i
    · subst k
      rw [idealSheaf_comap_map_openImmersion]
    · rw [idealSheaf_comap_map_eq_top_of_disjoint_closed_image (j k) (j i) (hj k) (hd hki)]
      exact le_top

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
