module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-!
概要：終対象の頂点はホモトピー圏で互いに同型。
方針：slice 射影の持ち上げ性で辺と片側の逆射を作り、二単体の合成関係を使う。
規約：ホモトピー圏は A1 の橋により Mathlib の hoFunctor に移す。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の終対象の一意性と極限の一意性。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet SSet.Truncated SimplicialObject.Truncated
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：二つの点の join の左包含は標準辺の始点。
方針：Yoneda で零単体の有限計算へ帰着する。
規約：始点は δ₁。
使われ方：HTT §1.2.12 の錐の辺への変換。 -/
lemma joinStdSimplexIso_zero_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom = stdSimplex.δ 1 := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：二つの点の join の右包含は標準辺の終点。
方針：Yoneda で零単体の有限計算へ帰着する。
規約：終点は δ₀。
使われ方：HTT §1.2.12 の錐の辺への変換。 -/
lemma joinStdSimplexIso_zero_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom = stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：辺と点の join の左包含は標準三角形の最初の辺。
方針：Yoneda で有限順序写像の計算へ帰着する。
規約：右端の頂点を除く面 δ₂。
使われ方：HTT §1.2.12 の逆射を与える二単体。 -/
lemma joinStdSimplexIso_one_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom = stdSimplex.δ 2 := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：辺の端点で制限した join は、三角形の対応する右端の辺に写る。
方針：Yoneda で有限順序写像の計算へ帰着する。
規約：i=0 は右端の辺、i=1 は対角の辺。
使われ方：HTT §1.2.12 の逆射の二単体の面。 -/
lemma joinStdSimplexIso_one_vertex (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ i.castSucc := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  apply SSet.yonedaEquiv.injective
  fin_cases i <;> decide

/-- 概要：頂点上の slice の零単体から、その頂点へ向かう辺を得る。
方針：Δ[0]⋆Δ[0] の錐を Δ[1] に移し、両端を包含の式で比較する。
規約：始点は slice 射影の値、終点は固定された頂点 x。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の終対象への辺。 -/
def sliceOverVertexEdge {X : SSet.{u}} (x : X _⦋0⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) _⦋0⦌) :
    Edge (X := (truncation 2).obj X)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ) x where
  edge := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ σ.val)
  src_eq := by
    change X.δ 1 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  tgt_eq := by
    change X.δ 0 (SSet.yonedaEquiv _) = x
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id_assoc,
      σ.property, Equiv.apply_symm_apply]

/-- 概要：終対象となる頂点への辺が任意の頂点から存在する。
方針：trivial Kan fibration である slice 射影の、空集合から点への単射に対する持ち上げを使う。
規約：quasicategory 性を仮定せず、境界充填条件だけを使う。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の終対象の一意性。 -/
lemma IsTerminalVertex.nonempty_edge {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (y : X _⦋0⦌) :
    Nonempty (Edge (X := (truncation 2).obj X) y x) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration x).1 hx
  let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  let a : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x) := Subcomplex.isInitialBot.to _
  let i : E ⟶ (Δ[0] : SSet.{u}) := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  have hi : Mono i := inferInstance
  have := ht.mem i hi
  have sq : CommSq a i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))
      (SSet.yonedaEquiv.symm y) := ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  let σ := SSet.yonedaEquiv sq.lift
  have hσ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ = y := by
    rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  have e := sliceOverVertexEdge x σ
  change Edge (X := (truncation 2).obj X)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ) x at e
  rw [hσ] at e
  exact ⟨e⟩

/-- 概要：slice の n 単体を錐として curry すると、その単体に対応する Yoneda 射になる。
方針：恒等単体における値を比較する。
規約：任意の図式と次数について成り立つ。
使われ方：HTT §1.2.12 の恒等錐の持ち上げ。 -/
lemma sliceOverCurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry σ.val σ.property = SSet.yonedaEquiv.symm σ := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u}))))
    (𝟙 K) ≫ σ.val = σ.val
  rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 概要：slice の単体に対応する Yoneda 射を uncurry すると、その錐自身になる。
方針：curry の Yoneda 表示と普遍性の両逆関係を使う。
規約：任意の図式と次数について成り立つ。
使われ方：HTT §1.2.12 の二単体の面の比較。 -/
lemma sliceOverUncurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (SSet.yonedaEquiv.symm σ) = σ.val := by
  rw [← sliceOverCurry_yoneda n σ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]

/-- 概要：恒等辺を与える定数錐は頂点上の slice の零単体。
方針：錐全体を x に定数で写す。
規約：射影も x を取る。
使われ方：HTT §1.2.12 の終対象の逆射の構成。 -/
def sliceIdentityCone {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm x)) _⦋0⦌ :=
  ⟨SSet.const x, by rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]⟩

/-- 概要：恒等錐の射影は元の頂点。
方針：定数射の Yoneda 表示を使う。
規約：恒等錐は x 上の slice の頂点。
使われ方：HTT §1.2.12 の端点を固定した持ち上げ。 -/
lemma sliceIdentityCone_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (sliceIdentityCone x) = x := by
  change SSet.yonedaEquiv (_ ≫ SSet.const x) = x
  rw [SSet.comp_const, SSet.yonedaEquiv_const]

/-- 概要：終対象から出る任意の辺は、恒等辺への合成二単体を持つ片側の逆射を持つ。
方針：始点で恒等錐を固定して slice 射影に沿い辺を持ち上げ、Δ[1]⋆Δ[0] を三角形に直す。
規約：quasicategory 性はこの構成には不要。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の二つの終対象の同型。 -/
lemma IsTerminalVertex.nonempty_split {X : SSet.{u}} {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (f : Edge (X := (truncation 2).obj X) x y) :
    Nonempty (Σ g : Edge (X := (truncation 2).obj X) y x,
      SSet.Truncated.Edge.CompStruct f g
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x)) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration x).1 hx
  let a := SSet.yonedaEquiv.symm (sliceIdentityCone x)
  let b : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm f.edge
  have := ht.mem (stdSimplex.δ (1 : Fin 2)) inferInstance
  have sq : CommSq a (stdSimplex.δ 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) b := by
    constructor
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, sliceIdentityCone_projection,
      stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [b]
    rw [Equiv.apply_symm_apply]
    exact f.src_eq.symm
  let c := sq.lift
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry c
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ L
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ F = b := by
    dsimp [F]
    rw [← joinStdSimplexIso_one_inl, Category.assoc, Iso.hom_inv_id_assoc]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection c).trans sq.fac_right
  have hv (i : Fin 2) : stdSimplex.δ i.castSucc ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0]) ≫ L) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← joinStdSimplexIso_one_vertex, Category.assoc]
    dsimp [F]
    rw [Iso.hom_inv_id_assoc]
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ F = SSet.const x := by
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry sq.fac_left
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, sliceOverUncurry_yoneda] at he
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc from rfl, hv, he]
    exact SSet.comp_const _ x
  let z := SSet.yonedaEquiv F
  have hz₂ : X.δ (2 : Fin 3) z = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₂]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have hz₁ : X.δ (1 : Fin 3) z = (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₁]
    change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op x =
      X.map (SimplexCategory.σ (0 : Fin 1)).op x
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ ↦ X.map α.op x) (by decide)
  have hsrc : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) z) = y := by
    have he : X.δ (1 : Fin 2) (X.δ (0 : Fin 3) z) =
        X.δ (0 : Fin 2) (X.δ (2 : Fin 3) z) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op z)
      decide
    rw [he, hz₂]
    exact f.tgt_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) z) = x := by
    have he : X.δ (0 : Fin 2) (X.δ (0 : Fin 3) z) =
        X.δ (0 : Fin 2) (X.δ (1 : Fin 3) z) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op z)
      decide
    rw [he, hz₁]
    exact (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).tgt_eq
  let g : Edge (X := (truncation 2).obj X) y x := ⟨X.δ 0 z, hsrc, htgt⟩
  exact ⟨⟨g, ⟨z, hz₂, rfl, hz₁⟩⟩⟩

/-- 概要：二つの終対象となる頂点は辺のホモトピー類による圏で同型。
方針：一方への辺に片側逆射を作り、さらにその逆射の片側逆射を作って両側逆射に直す。
規約：X は Mathlib の quasicategory。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の終対象の一意性。 -/
noncomputable def terminalVertexIso₂ {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y) :
    HomotopyCategory₂.mk (A := (truncation 2).obj X) x ≅ HomotopyCategory₂.mk y := by
  let f := Classical.choice (hy.nonempty_edge x)
  let sg := Classical.choice (hx.nonempty_split f)
  let g := sg.1
  let sk := Classical.choice (hy.nonempty_split g)
  let k := sk.1
  have hg : HomotopyCategory₂.homMk f ≫ HomotopyCategory₂.homMk g =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) x) := sg.2.homotopyCategory₂_fac
  have hk : HomotopyCategory₂.homMk g ≫ HomotopyCategory₂.homMk k =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) y) := sk.2.homotopyCategory₂_fac
  have hf : HomotopyCategory₂.homMk f = HomotopyCategory₂.homMk k := by
    calc
      _ = HomotopyCategory₂.homMk f ≫ (HomotopyCategory₂.homMk g ≫
          HomotopyCategory₂.homMk k) := by rw [hk, Category.comp_id]
      _ = (HomotopyCategory₂.homMk f ≫ HomotopyCategory₂.homMk g) ≫
          HomotopyCategory₂.homMk k := (Category.assoc _ _ _).symm
      _ = HomotopyCategory₂.homMk k := by rw [hg, Category.id_comp]
  exact ⟨HomotopyCategory₂.homMk f, HomotopyCategory₂.homMk g, hg, by rw [hf]; exact hk⟩

/-- 概要：二つの終対象となる頂点は Mathlib のホモトピー圏 hX で同型。
方針：辺の商での同型を A1 の比較同値の関手で写す。
規約：X は Mathlib の quasicategory、追加のモデル構造は不要。
使われ方：HTT §1.2.12、極限の h(slice) での一意性。 -/
noncomputable def terminalVertexIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex y) :
    (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor.mapIso (terminalVertexIso₂ hx hy)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
