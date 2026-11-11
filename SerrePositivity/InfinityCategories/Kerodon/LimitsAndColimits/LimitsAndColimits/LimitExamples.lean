module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：通常の圏の nerve における極限の具体的な検算。
方針：標準辺の最後の頂点への定数図式の slice を計算し、二対象離散図式の通常の極限と照合する。
規約：具体例の通常の圏は二対象の順序圏 0→1。一般の圏の全極限の比較は主張しない。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の通常の圏との整合性の検算。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace LimitChecks

/-- 概要：標準単体への二つの射は、全ての頂点で等しければ等しい。
方針：各単体の各頂点への制限の自然性を使う。
規約：標準単体の次数 n は任意。
使われ方：HTT §1.2.13 の順序圏の nerve への錐の一意性。 -/
lemma hom_ext_to_stdSimplex {A : SSet.{u}} {n : ℕ} (f g : A ⟶ Δ[n])
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  let α := (SimplexCategory.const ⦋0⦌ ⦋d⦌ i).op
  have hf := ConcreteCategory.congr_hom (f.naturality α) a
  have hg := ConcreteCategory.congr_hom (g.naturality α) a
  have h₀ := ConcreteCategory.congr_hom h (A.map α a)
  exact congrArg (fun z : (Δ[n] : SSet.{u}) _⦋0⦌ ↦ z 0) (hf.symm.trans (h₀.trans hg))

/-- 概要：join から標準単体への射は左右の因子への制限で決まる。
方針：join の零単体が左右の零単体の直和であることと、標準単体への射の頂点による一意性を使う。
規約：標的は標準単体なので任意の単体集合への射の一意性は主張しない。
使われ方：HTT §1.2.13 の標準辺上の定数錐の一意性。 -/
lemma join_hom_ext_to_stdSimplex {A B : SSet.{u}} {n : ℕ} (f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ Δ[n])
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ g)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ g) : f = g := by
  apply hom_ext_to_stdSimplex
  apply ConcreteCategory.hom_ext
  rintro ⟨ℓ, a, b⟩
  fin_cases ℓ
  · cases a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hB (Opposite.op ⦋0⦌)) b
  · cases b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hA (Opposite.op ⦋0⦌)) a

/-- 概要：標準辺の最後に点を join した錐を、最後の二頂点を重ねて辺へ戻す。
方針：Δ[1]⋆Δ[0]≅Δ[2] と σ₁ を合成する。
規約：左の辺は恒等、右の点は最後の頂点へ写る。
使われ方：HTT §1.2.13 の終対象 1 への定数図式の錐の構成。 -/
def intervalTerminalExtension : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ 1

/-- 概要：標準辺の終対象錐を左因子へ制限すると恒等。
方針：有限順序写像の計算を使う。
規約：左因子は Δ[1]。
使われ方：HTT §1.2.13 の錐の頂点への制限。 -/
lemma intervalTerminalExtension_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ intervalTerminalExtension = 𝟙 Δ[1] := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：標準辺の終対象錐を右因子へ制限すると最後の頂点。
方針：有限順序写像の計算を使う。
規約：右因子は Δ[0]。
使われ方：HTT §1.2.13 の終対象への固定条件。 -/
lemma intervalTerminalExtension_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet.{u}) Δ[0] ≫ intervalTerminalExtension =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：標準辺の最後の頂点を値とする任意の形 K の定数図式。
方針：SSet.const を使う。
規約：K の空・非空を問わない。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の終対象への定数図式の極限。 -/
def intervalTerminalDiagram (K : SSet.{u}) : K ⟶ (Δ[1] : SSet.{u}) :=
  SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 概要：標準辺の最後の頂点への定数図式の slice 射影は同型。
方針：左の単体と右の定数値が錐を一意に決め、明示的な終対象錐で全射性を示す。
規約：任意の単体集合 K、全次数での同型。
使われ方：HTT §1.2.13 の終対象への定数図式の極限の検算。 -/
lemma intervalTerminalProjection_isIso (K : SSet.{u}) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (intervalTerminalDiagram K)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro σ τ h
    apply Subtype.ext
    apply join_hom_ext_to_stdSimplex
    · exact SSet.yonedaEquiv.injective h
    · exact σ.property.trans τ.property.symm
  · intro a
    let τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (intervalTerminalDiagram K)) _⦋n⦌ :=
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ intervalTerminalExtension, by
        rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
          intervalTerminalExtension_inr, SSet.comp_const]
        rfl⟩
    refine ⟨τ, ?_⟩
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] K ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ intervalTerminalExtension)) = a
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, intervalTerminalExtension_inl,
      Category.comp_id, Equiv.apply_symm_apply]

/-- 概要：標準辺の最後の頂点は終対象の境界充填条件を満たす。
方針：その頂点上の slice 射影が同型なので trivial Kan fibration である。
規約：quasicategory 性を別途仮定する必要はない。
使われ方：HTT §1.2.12、通常の圏 0→1 の終対象 1 の検算。 -/
lemma intervalLast_isTerminal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 2)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration, SSet.yonedaEquiv_symm_zero]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (intervalTerminalDiagram (Δ[0] : SSet.{u})))
  have := intervalTerminalProjection_isIso (Δ[0] : SSet.{u})
  infer_instance

/-- 概要：終対象 1 への定数図式の定数錐。
方針：錐全体を最後の頂点に定数で写す。
規約：任意の形 K に対して定義する。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の通常の極限との比較。 -/
def intervalTerminalCone (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (intervalTerminalDiagram K) :=
  ⟨SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)), by rw [SSet.comp_const]; rfl⟩

/-- 概要：標準辺の終対象 1 への任意の定数図式の定数錐は極限錐。
方針：slice 射影の同型と終対象性の反映を使う。
規約：K は任意で、空の図式も含む。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の定数図式の極限の検算。 -/
lemma intervalTerminalCone_isLimit (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (intervalTerminalCone K) := by
  have := intervalTerminalProjection_isIso K
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (intervalTerminalDiagram K))
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (intervalTerminalDiagram K)).app (Opposite.op ⦋0⦌)
      (intervalTerminalCone K) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    change SSet.yonedaEquiv (_ ≫ SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _
    rw [SSet.comp_const, SSet.yonedaEquiv_const]
  rw [he]
  exact intervalLast_isTerminal

/-- 概要：標準辺の頂点 v から終対象 1 への定数図式に付く錐。
方針：標準辺の終対象錐を v と右因子の唯一の点の射で引き戻す。
規約：v=0 と v=1 の両方の錐を定義する。
使われ方：HTT §1.2.13 の通常の圏と nerve の極限性の正例・負例。 -/
def intervalConeAtVertex (K : SSet.{u}) (v : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (intervalTerminalDiagram K) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm v))
    (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ intervalTerminalExtension, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc,
      intervalTerminalExtension_inr, SSet.comp_const]
    rfl⟩

/-- 概要：v からの定数図式への錐の頂点は v。
方針：左因子への制限と標準辺の終対象錐の恒等式を使う。
規約：任意の形 K。
使われ方：HTT §1.2.13 の通常の錐との頂点の一致。 -/
lemma intervalConeAtVertex_vertex (K : SSet.{u}) (v : Fin 2) :
    (intervalConeAtVertex K v).vertex = stdSimplex.obj₀Equiv.symm v := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm v))
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫ intervalTerminalExtension)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, intervalTerminalExtension_inl,
    Category.comp_id, SSet.yonedaEquiv_const]

/-- 概要：1 を頂点に持つ定数図式への錐は極限錐。
方針：slice 射影の同型が終対象性を反映することを使う。
規約：任意の形 K。
使われ方：HTT §1.2.13 の二対象離散図式の積の正例。 -/
lemma intervalConeAtVertex_one_isLimit (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (intervalConeAtVertex K 1) := by
  have := intervalTerminalProjection_isIso K
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (intervalTerminalDiagram K))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (intervalConeAtVertex K 1).vertex
  rw [intervalConeAtVertex_vertex]
  exact intervalLast_isTerminal

/-- 概要：具体例に使う通常の圏 0→1 の終対象。
方針：二元順序集合の最後の元を ULift して標準単体の nerve 表示に合わせる。
規約：この有限例は宇宙 0。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の二項積の検算。 -/
def walkingArrowTop : ULift.{0} (Fin 2) := ⟨1⟩

/-- 概要：通常の圏 0→1 の二つの終対象からなる離散図式。
方針：Bool の離散圏から値 1 の定数関手を取る。
規約：空でない二対象の積の図式。
使われ方：HTT §1.2.13 の通常の二項積と nerve の比較。 -/
def topPairDiagram : Discrete Bool ⥤ ULift.{0} (Fin 2) :=
  (Functor.const (Discrete Bool)).obj walkingArrowTop

/-- 概要：v から通常の圏の二対象の定数図式への錐。
方針：各脚を唯一の射 v→1 にする。
規約：v=0 と v=1 の全ての通常の錐の頂点を試験する。
使われ方：HTT §1.2.13 の積の普遍性の検算。 -/
def topPairOrdinaryCone (v : Fin 2) : Limits.Cone topPairDiagram where
  pt := ULift.up v
  π :=
    { app _ := homOfLE (show ULift.up v ≤ walkingArrowTop from v.le_last)
      naturality _ _ _ := Subsingleton.elim _ _ }

/-- 概要：通常の圏 0→1 で 1 からの錐は 1 と 1 の積。
方針：任意の錐の頂点から 1 への唯一の射が普遍射になる。
規約：Mathlib の通常の IsLimit を用いる。
使われ方：HTT §1.2.13 の nerve での極限との正例の照合。 -/
def topPairOrdinaryCone_one_isLimit : Limits.IsLimit (topPairOrdinaryCone 1) where
  lift s := homOfLE (show s.pt ≤ ULift.up (1 : Fin 2) from s.pt.down.le_last)
  fac _ _ := Subsingleton.elim _ _
  uniq _ _ _ := Subsingleton.elim _ _

/-- 概要：通常の二対象離散図式への v からの錐が極限であることは v=1 と同値。
方針：普遍性を 1 からの錐に適用して 1≤v を得る。
規約：0 からの錐は極限でないという負例も含む。
使われ方：HTT §1.2.13 の通常の極限の具体的判定。 -/
lemma topPairOrdinaryCone_isLimit_iff (v : Fin 2) :
    Nonempty (Limits.IsLimit (topPairOrdinaryCone v)) ↔ v = 1 := by
  constructor
  · rintro ⟨h⟩
    have hv : (1 : Fin 2) ≤ v := leOfHom (h.lift (topPairOrdinaryCone 1))
    exact le_antisymm v.le_last hv
  · rintro rfl
    exact ⟨topPairOrdinaryCone_one_isLimit⟩

/-- 概要：通常の二対象の定数図式の nerve は、標準辺の定数図式を nerve の同型で写したもの。
方針：各射列の対象の値を比較し、順序圏の射の一意性を使う。
規約：単体集合は宇宙 0。
使われ方：HTT §1.2.13 の比較する二つの図式の同定。 -/
lemma topPairDiagram_nerve_eq :
    nerveMap topPairDiagram = intervalTerminalDiagram (nerve (Discrete Bool)) ≫
      (stdSimplex.isoNerve.{0} 1).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.nerve.ext_of_isThin
  rfl

/-- 概要：通常の v からの二対象の定数図式への錐に対応する nerve の join の錐。
方針：標準辺上の錐を標準単体と nerve の同型で写し、図式の等式で移送する。
規約：通常の錐と図式・頂点の両方を照合する。
使われ方：HTT §1.2.13 の通常の極限との比較例。 -/
def topPairNerveCone (v : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (nerveMap topPairDiagram) :=
  ((intervalConeAtVertex (nerve (Discrete Bool)) v).postcomp (stdSimplex.isoNerve.{0} 1).hom).cast
    topPairDiagram_nerve_eq.symm

/-- 概要：nerve の錐の頂点は通常の錐と同じ v の頂点。
方針：錐の後合成と図式の移送の頂点の式を使う。
規約：nerveEquiv は通常の対象と零単体の同値。
使われ方：HTT §1.2.13 の同じ錐の比較であることの確認。 -/
lemma topPairNerveCone_vertex (v : Fin 2) :
    (topPairNerveCone v).vertex = CategoryTheory.nerveEquiv.symm (ULift.up v) := by
  rw [topPairNerveCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_cast, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_postcomp, intervalConeAtVertex_vertex]
  exact ComposableArrows.ext₀ rfl

/-- 概要：nerve においても 1 からの二対象の定数図式への錐は極限。
方針：標準辺上の極限錐を同型で移す。
規約：通常の極限性を仮定せず単体集合側で検証する。
使われ方：HTT §1.2.13 の通常の二項積との正例の照合。 -/
lemma topPairNerveCone_one_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (topPairNerveCone 1) :=
  ((intervalConeAtVertex_one_isLimit (nerve (Discrete Bool))).postcomp_of_isIso
    (stdSimplex.isoNerve.{0} 1).hom).cast topPairDiagram_nerve_eq.symm

/-- 概要：nerve の二対象離散図式への v からの錐が極限であることは v=1 と同値。
方針：極限の頂点の一意性から h(nerve C) の同型を得て、nerve への射から復元する関手で通常の順序圏へ戻す。
規約：v=0 の非極限性も単体集合側から証明する。
使われ方：HTT §1.2.13 の通常の極限との正例・負例の一致。 -/
lemma topPairNerveCone_isLimit_iff (v : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (topPairNerveCone v) ↔ v = 1 := by
  constructor
  · intro h
    let e := (eqToIso (congrArg SSet.HomotopyCategory.mk (topPairNerveCone_vertex v)).symm) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso (topPairNerveCone v) (topPairNerveCone 1) h topPairNerveCone_one_isLimit ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk (topPairNerveCone_vertex 1))
    let E := SSet.Truncated.HomotopyCategory.descOfTruncation
      (𝟙 ((truncation 2).obj (nerve (ULift.{0} (Fin 2)))))
    let eC := E.mapIso e
    change (ULift.up v : ULift.{0} (Fin 2)) ≅ ULift.up (1 : Fin 2) at eC
    have hv : (1 : Fin 2) ≤ v := leOfHom eC.inv
    exact le_antisymm v.le_last hv
  · rintro rfl
    exact topPairNerveCone_one_isLimit

/-- 概要：通常の圏 0→1 の二項積の極限性と、その nerve の極限錐の条件が一致する。
方針：両側を同じ頂点の条件 v=1 に帰着する。
規約：v=0 と v=1 の全ての錐を比較し、図式・頂点の一致も別途証明済み。
使われ方：HTT §1.2.13、Kerodon §7.1（Tag 02H1） の通常の圏との整合性の具体的検算。 -/
lemma topPair_limit_agreement (v : Fin 2) :
    Nonempty (Limits.IsLimit (topPairOrdinaryCone v)) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (topPairNerveCone v) :=
  (topPairOrdinaryCone_isLimit_iff v).trans (topPairNerveCone_isLimit_iff v).symm

end LimitChecks
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
