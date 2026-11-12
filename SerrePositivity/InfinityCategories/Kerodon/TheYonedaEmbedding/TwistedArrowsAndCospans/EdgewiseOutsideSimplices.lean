module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.StandardSimplexSupports
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing

/-!
概要：edgewise の延長領域の外の非退化単体と有限頂点集合の対応。
方針：標準単体の頂点集合による全単射を領域外の条件に制限する。
規約：右射影の同値性はまだ結論に含めない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、有限頂点集合の対を単体的 pairing へ移す。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：標準単体の非退化単体の頂点集合は全頂点の像。
方針：次数ごとの頂点集合の同値の順方向の定義を計算する。
規約：次元の証明の選択には依存しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、部分複体の所属条件との照合。 -/
lemma stdSimplexNondegenerateSupport_eq_image {n : ℕ} (s : (Δ[n] : SSet.{u}).N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s = Finset.univ.image s.simplex := by
  ext j
  change j ∈ (stdSimplex.nonDegenerateEquiv' ⟨s.simplex, s.nonDegenerate⟩).val ↔ _
  rw [stdSimplex.nonDegenerateEquiv'_iff]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

/-- 概要：非退化単体の延長領域への所属は頂点集合の領域条件と一致する。
方針：一般の単体の頂点像の所属判定を使う。
規約：任意の非退化次元を一つの型 N で扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、領域外の条件の移送。 -/
lemma edgewiseNondegenerate_mem_iff_support {n : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}).N) :
    s.simplex ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).obj (Opposite.op ⦋s.dim⦌) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSupportInDomain n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s) := by
  rw [stdSimplexNondegenerateSupport_eq_image]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.mem_edgewiseRightExtensionDomain_iff_support s.simplex

/-- 概要：領域外の非退化単体から領域外の頂点集合を取り出す。
方針：頂点集合への写像と領域条件の同値を使う。
規約：部分複体の外の条件を保持した型同士の写像。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、単体的 pairing の有限集合表示。 -/
noncomputable def edgewiseOutsideSimplexSupport {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain.{u} n).N) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOutsideSupport n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport s.toN, fun h ↦
    s.notMem ((edgewiseNondegenerate_mem_iff_support s.toN).2 h)⟩

/-- 概要：領域外の非退化単体から頂点集合への写像は全単射。
方針：全非退化単体の一意性を制限し、領域外の頂点集合の非空性を左頂点から得る。
規約：逆方向では領域外の条件を所属判定で戻す。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の両型の全単射の移送。 -/
lemma edgewiseOutsideSimplexSupport_bijective (n : ℕ) :
    Function.Bijective (edgewiseOutsideSimplexSupport.{u} (n := n)) := by
  constructor
  · intro s t h
    apply (Subcomplex.N.ext_iff s t).2
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport_injective _ (congrArg Subtype.val h)
  · intro S
    have hne : S.val.Nonempty := ⟨_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSupportPivot_mem S.val S.property⟩
    let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupportEquiv.{u} (n + n + 1)).symm ⟨S.val, hne⟩
    have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport x = S.val :=
      congrArg Subtype.val ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupportEquiv (n + n + 1)).apply_symm_apply
        ⟨S.val, hne⟩)
    have hn : x.simplex ∉ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain n).obj (Opposite.op ⦋x.dim⦌) := by
      rw [edgewiseNondegenerate_mem_iff_support, hx]
      exact S.property
    refine ⟨Subcomplex.N.mk' x hn, ?_⟩
    apply Subtype.ext
    exact hx

/-- 概要：領域外の非退化単体と領域外の頂点集合の全単射。
方針：頂点集合を取る全単射を同値にまとめる。
規約：順方向は既存の頂点集合の取り出しそのもの。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、有限集合の pairing を移送する同値。 -/
noncomputable def edgewiseOutsideSimplexEquiv (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightExtensionDomain.{u} n).N ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOutsideSupport n :=
  Equiv.ofBijective edgewiseOutsideSimplexSupport (edgewiseOutsideSimplexSupport_bijective n)

/-- 概要：頂点集合の逆像の非退化単体は元の頂点集合を回収する。
方針：領域外の全単射の往復の等式の値を取る。
規約：逆の単体の次元は頂点数から決まる。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、pairing の像の面と順位の計算。 -/
lemma edgewiseOutsideSimplexEquiv_symm_support (n : ℕ) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOutsideSupport n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.stdSimplexNondegenerateSupport ((edgewiseOutsideSimplexEquiv.{u} n).symm S).toN = S.val :=
  congrArg Subtype.val ((edgewiseOutsideSimplexEquiv n).apply_symm_apply S)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
