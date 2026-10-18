module
public import SerrePositivity.InfinityCategories.Derived.SquareLegCompatibility
public import SerrePositivity.InfinityCategories.DGNerve.FiberConeComparison
public import SerrePositivity.InfinityCategories.DGNerve.ComplexSimplexArrow

/-! # 複体 dg nerve の辺と指定射の計算

概要：辺の一単体の一致から鎖写像を同定し、標準 fiber 錐の脚を元の射影へ同定する。
方針：閉零元の比較と端点の等式を消去し、標準四角形の二つの三角形を評価する。
規約：端点の移送は異種等号で記録する。使われ方：D6a の指定四辺の長完全列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open DGNerve.HomotopyComparison CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：鎖写像から作った辺を読み戻すと元の鎖写像になる。
方針：辺の閉零元の評価と鎖写像の cochain の単射性を使う。
規約：端点は対応する複体の頂点。使われ方：指定した射の同定。 -/
lemma derived_edgeChainMap_complexEdge {K L : Complex S} (f : K ⟶ L) :
    edgeChainMap (complexEdge f).toTruncated = f := by
  apply Cochain.ofHom_injective
  rw [edgeChainMap, complexClosedHomEquiv_cochain]
  exact (congrArg Subtype.val (edgeClosed_cycle (complexEdge f).toTruncated)).trans
    (complexEdge_cycle f)

/-- 概要：一単体が指定鎖写像の辺と等しければ、読み取った鎖写像は元の射と異種等号で等しい。
方針：両端点の面の等式を消去し、端点付き辺の外延性と読み戻しの公式を使う。
規約：元の端点の複体を変更せずに述べる。使われ方：標準錐の射影の同定。 -/
lemma derived_edgeChainMap_heq_complexEdge
    {x y : (dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x y)
    {K L : Complex S} (f : K ⟶ L) (he : e.edge = (complexEdge f).edge) :
    HEq (edgeChainMap e) f := by
  have hs : x = Simplex.vertex K := by
    have hh := congrArg (fun s : Simplex S (Complex S) 1 => (dgNerve S (Complex S)).δ 1 s) he
    exact e.src_eq.symm.trans (hh.trans (complexEdge f).src_eq)
  have ht : y = Simplex.vertex L := by
    have hh := congrArg (fun s : Simplex S (Complex S) 1 => (dgNerve S (Complex S)).δ 0 s) he
    exact e.tgt_eq.symm.trans (hh.trans (complexEdge f).tgt_eq)
  subst x y
  have heq : e = (complexEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact he
  rw [heq, derived_edgeChainMap_complexEdge]

/-- 概要：指定鎖写像の一単体と一致する辺は、始域・終域を含め同じ arrow を与える。
方針：面写像で両端点を同定し、端点付き辺の外延性で置換する。
規約：arrow の等式は両端の複体の等式も含む。使われ方：射影の端点の正規化。 -/
lemma derived_edgeChainMap_arrow_eq_complexEdge
    {x y : (dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x y)
    {K L : Complex S} (f : K ⟶ L) (he : e.edge = (complexEdge f).edge) :
    Arrow.mk (edgeChainMap e) = Arrow.mk f := by
  have hs : x = Simplex.vertex K := by
    have hh := congrArg (fun s : Simplex S (Complex S) 1 => (dgNerve S (Complex S)).δ 1 s) he
    exact e.src_eq.symm.trans (hh.trans (complexEdge f).src_eq)
  have ht : y = Simplex.vertex L := by
    have hh := congrArg (fun s : Simplex S (Complex S) 1 => (dgNerve S (Complex S)).δ 0 s) he
    exact e.tgt_eq.symm.trans (hh.trans (complexEdge f).tgt_eq)
  subst x y
  have heq : e = (complexEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact he
  rw [heq, derived_edgeChainMap_complexEdge]

/-- 概要：端点付き辺から鎖写像を取り出して戻すと元の一単体になる。
方針：端点を面写像で置換し、閉零成分の評価と一単体の復元公式を使う。
規約：端点の表記に依存しない。使われ方：指定された四辺を鎖写像へ正規化する。 -/
lemma derived_complexEdge_edgeChainMap
    {x y : (dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x y) :
    (complexEdge (edgeChainMap e)).edge = e.edge := by
  rcases e with ⟨s, hs, ht⟩
  subst x y
  have hh : edgeChainMap (⟨s, rfl, rfl⟩ : SSet.Truncated.Edge
      (X := twoTruncation S (Complex S)) _ _) = simplexChainMap s := by
    apply Cochain.ofHom_injective
    rw [edgeChainMap, complexClosedHomEquiv_cochain, simplexChainMap_cochain]
    exact (congrArg Subtype.val (edgeClosed_cycle
      (⟨s, rfl, rfl⟩ : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) _ _))).trans
        (eq_of_heq (edgeCycle_val_heq _))
  rw [hh]
  exact complexEdge_simplexChainMap s

/-- 概要：合成三角形の三つの鎖写像は複体ホモトピー圏で合成する。
方針：N3 と複体ホモトピー圏の比較を三角形の合成関係に適用する。
規約：代表鎖写像の厳密な可換性ではなくホモトピー類での等式。使われ方：指定脚の比較。 -/
lemma derived_edgeChainMap_comp
    {x y z : (dgNerve S (Complex S)) _⦋0⦌}
    {e : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x y}
    {f : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) y z}
    {g : SSet.Truncated.Edge (X := twoTruncation S (Complex S)) x z}
    (t : SSet.Truncated.Edge.CompStruct e f g) :
    (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map
      (edgeChainMap e ≫ edgeChainMap f) =
      (_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).map (edgeChainMap g) := by
  rw [Functor.map_comp, edgeChainMap_quotient, edgeChainMap_quotient, edgeChainMap_quotient,
    ← Functor.map_comp, ← Functor.map_comp, t.homotopyCategory₂_fac]

variable {B C D : Complex S}

/-- 概要：標準 fiber 四角形の下辺は第一射影である。
方針：下側三角形の最初の辺を評価する。
規約：射影の符号を保持する。使われ方：fiber 列の第一成分。 -/
lemma derived_standardFiberSquare_bottom (g : B ⟶ D) (h : C ⟶ D) :
    derivedSquareBottomEdge ≫ standardFiberSquare g h =
      SSet.yonedaEquiv.symm (complexEdge (pullbackProjectionB g h)).edge := by
  rw [← derivedSquareTriangle_bottom, Category.assoc, standardFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (fiberLowerTriangle g h).d₂]

/-- 概要：標準 fiber 四角形の左辺は第二射影である。
方針：上側三角形の最初の辺を評価する。
規約：射影の符号を保持する。使われ方：fiber 列の第二成分。 -/
lemma derived_standardFiberSquare_left (g : B ⟶ D) (h : C ⟶ D) :
    derivedSquareLeftEdge ≫ standardFiberSquare g h =
      SSet.yonedaEquiv.symm (complexEdge (pullbackProjectionC g h)).edge := by
  rw [← derivedSquareTriangle_left, Category.assoc, standardFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (fiberUpperTriangle g h).d₂]

/-- 概要：標準 fiber 錐の第一脚の鎖写像は第一射影である。
方針：脚と下辺の一致および標準四角形の第一射影の式を使う。
規約：端点の同定を異種等号に吸収する。使われ方：比較三角形を第一射影へ移す。 -/
lemma derived_standardFiberCone_leg_bottom (g : B ⟶ D) (h : C ⟶ D) :
    HEq (edgeChainMap (derivedConeLeg (standardFiberCone g h)
      (SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ SSet.horn₂₂.ι₀₂))))
      (pullbackProjectionB g h) := by
  apply derived_edgeChainMap_heq_complexEdge
  exact (derivedConeLeg_pullback_bottom (standardFiberSquare g h)).trans
    ((congrArg SSet.yonedaEquiv (derived_standardFiberSquare_bottom g h)).trans
      (SSet.yonedaEquiv.apply_symm_apply _))

/-- 概要：標準 fiber 錐の第二脚の鎖写像は第二射影である。
方針：脚と左辺の一致および標準四角形の第二射影の式を使う。
規約：端点の同定を異種等号に吸収する。使われ方：比較三角形を第二射影へ移す。 -/
lemma derived_standardFiberCone_leg_left (g : B ⟶ D) (h : C ⟶ D) :
    HEq (edgeChainMap (derivedConeLeg (standardFiberCone g h)
      (SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ SSet.horn₂₂.ι₁₂))))
      (pullbackProjectionC g h) := by
  apply derived_edgeChainMap_heq_complexEdge
  exact (derivedConeLeg_pullback_left (standardFiberSquare g h)).trans
    ((congrArg SSet.yonedaEquiv (derived_standardFiberSquare_left g h)).trans
      (SSet.yonedaEquiv.apply_symm_apply _))

end SerrePositivity.InfinityCategories
