module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SquareLegCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexSimplexArrow

/-! # 複体 dg nerve の辺と指定射の計算

概要：辺の一単体の一致から鎖写像を同定し、標準 fiber 錐の脚を元の射影へ同定する。
方針：閉零元の比較と端点の等式を消去し、標準四角形の二つの三角形を評価する。
規約：端点の移送は異種等号で記録する。使われ方：D6a の指定四辺の長完全列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes
open _root_.CategoryTheory MonoidalCategory _root_.SerrePositivity.DifferentialGraded
open _root_.CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：鎖写像から作った辺を読み戻すと元の鎖写像になる。
方針：辺の閉零元の評価と鎖写像の cochain の単射性を使う。
規約：端点は対応する複体の頂点。使われ方：指定した射の同定。 -/
lemma derived_edgeChainMap_complexEdge {K L : _root_.SerrePositivity.DifferentialGraded.Complex S} (f : K ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).toTruncated = f := by
  apply Cochain.ofHom_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap, complexClosedHomEquiv_cochain]
  exact (congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).toTruncated)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_cycle f)

/-- 概要：一単体が指定鎖写像の辺と等しければ、読み取った鎖写像は元の射と異種等号で等しい。
方針：両端点の面の等式を消去し、端点付き辺の外延性と読み戻しの公式を使う。
規約：元の端点の複体を変更せずに述べる。使われ方：標準錐の射影の同定。 -/
lemma derived_edgeChainMap_heq_complexEdge
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x y)
    {K L : Complex S} (f : K ⟶ L) (he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap e) f := by
  have hs : x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex K := by
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 1 s) he
    exact e.src_eq.symm.trans (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).src_eq)
  have ht : y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex L := by
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 0 s) he
    exact e.tgt_eq.symm.trans (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).tgt_eq)
  subst x y
  have heq : e = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact he
  rw [heq, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_complexEdge]

/-- 概要：指定鎖写像の一単体と一致する辺は、始域・終域を含め同じ arrow を与える。
方針：面写像で両端点を同定し、端点付き辺の外延性で置換する。
規約：arrow の等式は両端の複体の等式も含む。使われ方：射影の端点の正規化。 -/
lemma derived_edgeChainMap_arrow_eq_complexEdge
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x y)
    {K L : Complex S} (f : K ⟶ L) (he : e.edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap e) = Arrow.mk f := by
  have hs : x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex K := by
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 1 s) he
    exact e.src_eq.symm.trans (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).src_eq)
  have ht : y = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex L := by
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 0 s) he
    exact e.tgt_eq.symm.trans (hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).tgt_eq)
  subst x y
  have heq : e = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact he
  rw [heq, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_complexEdge]

/-- 概要：端点付き辺から鎖写像を取り出して戻すと元の一単体になる。
方針：端点を面写像で置換し、閉零成分の評価と一単体の復元公式を使う。
規約：端点の表記に依存しない。使われ方：指定された四辺を鎖写像へ正規化する。 -/
lemma derived_complexEdge_edgeChainMap
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap e)).edge = e.edge := by
  rcases e with ⟨s, hs, ht⟩
  subst x y
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (⟨s, rfl, rfl⟩ : SSet.Truncated.Edge
      (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) _ _) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s := by
    apply Cochain.ofHom_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap, complexClosedHomEquiv_cochain, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap_cochain]
    exact (congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle
      (⟨s, rfl, rfl⟩ : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) _ _))).trans
        (eq_of_heq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq _))
  rw [hh]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap s

/-- 概要：合成三角形の三つの鎖写像は複体ホモトピー圏で合成する。
方針：N3 と複体ホモトピー圏の比較を三角形の合成関係に適用する。
規約：代表鎖写像の厳密な可換性ではなくホモトピー類での等式。使われ方：指定脚の比較。 -/
lemma derived_edgeChainMap_comp
    {x y z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    {e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x y}
    {f : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) y z}
    {g : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap f) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap g) := by
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient,
    ← Functor.map_comp, ← Functor.map_comp, t.homotopyCategory₂_fac]

variable {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：標準 fiber 四角形の下辺は第一射影である。
方針：下側三角形の最初の辺を評価する。
規約：射影の符号を保持する。使われ方：fiber 列の第一成分。 -/
lemma derived_standardFiberSquare_bottom (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTriangle_bottom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberLowerTriangle g h).d₂]

/-- 概要：標準 fiber 四角形の左辺は第二射影である。
方針：上側三角形の最初の辺を評価する。
規約：射影の符号を保持する。使われ方：fiber 列の第二成分。 -/
lemma derived_standardFiberSquare_left (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareTriangle_left, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberUpperTriangle g h).d₂]

/-- 概要：標準 fiber 錐の第一脚の鎖写像は第一射影である。
方針：脚と下辺の一致および標準四角形の第一射影の式を使う。
規約：端点の同定を異種等号に吸収する。使われ方：比較三角形を第一射影へ移す。 -/
lemma derived_standardFiberCone_leg_bottom (g : B ⟶ D) (h : C ⟶ D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)
      (SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ SSet.horn₂₂.ι₀₂))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_heq_complexEdge
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_bottom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)).trans
    ((congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_standardFiberSquare_bottom g h)).trans
      (SSet.yonedaEquiv.apply_symm_apply _))

/-- 概要：標準 fiber 錐の第二脚の鎖写像は第二射影である。
方針：脚と左辺の一致および標準四角形の第二射影の式を使う。
規約：端点の同定を異種等号に吸収する。使われ方：比較三角形を第二射影へ移す。 -/
lemma derived_standardFiberCone_leg_left (g : B ⟶ D) (h : C ⟶ D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.derivedConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)
      (SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ SSet.horn₂₂.ι₁₂))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_heq_complexEdge
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedConeLeg_pullback_left (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)).trans
    ((congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_standardFiberSquare_left g h)).trans
      (SSet.yonedaEquiv.apply_symm_apply _))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.2.2" (partial := special) "仮定：可換環上の dg 圏または加群複体（Lean が強い：任意の加法圏ではない）。結論：dg nerve の辺を閉次数 0 射と同定し、h の Hom を H⁰ と比べ、具体的な鎖写像を辺に対応させる（加群複体で一致）。"] _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_complexEdge
