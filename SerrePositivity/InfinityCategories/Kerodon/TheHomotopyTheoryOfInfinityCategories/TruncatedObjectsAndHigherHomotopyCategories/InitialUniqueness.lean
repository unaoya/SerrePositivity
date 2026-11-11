module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：始対象の頂点はホモトピー圏で互いに同型。
方針：coslice 射影の持ち上げ性で辺と片側の逆射を作り、二単体の合成関係を使う。
規約：終対象の一意性の左右双対を直接構成する。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の始対象の一意性。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet SSet.Truncated SimplicialObject.Truncated
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：点と辺の join の右包含は標準三角形の最後の辺。
方針：Yoneda で有限順序写像の計算へ帰着する。
規約：左端の頂点を除く面 δ₀。
使われ方：HTT §1.2.12 の始対象の逆射を与える二単体。 -/
lemma joinStdSimplexIso_one_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom = stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：右因子の端点で制限した join は三角形の左端を含む辺に写る。
方針：Yoneda で有限順序写像の計算へ帰着する。
規約：i=0 は対角の辺、i=1 は最初の辺。
使われ方：HTT §1.2.12 の始対象の逆射の二単体の面。 -/
lemma joinStdSimplexIso_vertex_one (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ i.succ := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  apply SSet.yonedaEquiv.injective
  fin_cases i <;> decide

/-- 概要：頂点下の coslice の零単体はその頂点から出る辺を与える。
方針：点同士の join を標準辺に直し、両端の制限を計算する。
規約：始点は x、終点は coslice 射影の値。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の始対象からの辺。 -/
def sliceUnderVertexEdge {X : SSet.{u}} (x : X _⦋0⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌) :
    Edge (X := (truncation 2).obj X) x
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ) where
  edge := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ σ.val)
  src_eq := by
    change X.δ 1 (SSet.yonedaEquiv _) = x
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl, Category.assoc, Iso.hom_inv_id_assoc,
      σ.property, Equiv.apply_symm_apply]
  tgt_eq := by
    change X.δ 0 (SSet.yonedaEquiv _) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr, Category.assoc, Iso.hom_inv_id_assoc]
    rfl

/-- 概要：始対象となる頂点から任意の頂点への辺が存在する。
方針：coslice 射影の trivial Kan fibration 性で空集合から点への単射を持ち上げる。
規約：quasicategory 性は仮定しない。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の始対象の一意性。 -/
lemma IsInitialVertex.nonempty_edge {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : X _⦋0⦌) :
    Nonempty (Edge (X := (truncation 2).obj X) x y) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration x).1 hx
  let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
  let a : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x) := Subcomplex.isInitialBot.to _
  let i : E ⟶ (Δ[0] : SSet.{u}) := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  have hi : Mono i := inferInstance
  have := ht.mem i hi
  have sq : CommSq a i (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (SSet.yonedaEquiv.symm y) := ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  let σ := SSet.yonedaEquiv sq.lift
  have hσ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ = y := by
    rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  have e := sliceUnderVertexEdge x σ
  change Edge (X := (truncation 2).obj X) x
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌) σ) at e
  rw [hσ] at e
  exact ⟨e⟩

/-- 概要：coslice の単体の curry は、その単体に対応する Yoneda 射。
方針：恒等単体における値を比較する。
規約：任意の図式と次数について成り立つ。
使われ方：HTT §1.2.12 の恒等錐の持ち上げの双対。 -/
lemma sliceUnderCurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry σ.val σ.property = SSet.yonedaEquiv.symm σ := by
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K)
    (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})))) ≫ σ.val = σ.val
  rw [Equiv.symm_apply_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

/-- 概要：coslice の単体に対応する Yoneda 射の uncurry は元の錐。
方針：curry の Yoneda 表示と普遍性の両逆関係を使う。
規約：任意の図式と次数について成り立つ。
使われ方：HTT §1.2.12 の二単体の面の比較の双対。 -/
lemma sliceUnderUncurry_yoneda {K X : SSet.{u}} {p : K ⟶ X} (n : ℕ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm σ) = σ.val := by
  rw [← sliceUnderCurry_yoneda n σ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_curry]

/-- 概要：恒等辺を与える定数錐は頂点下の coslice の零単体。
方針：錐全体を x に定数で写す。
規約：射影も x を取る。
使われ方：HTT §1.2.12 の始対象の逆射の構成。 -/
def cosliceIdentityCone {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌ :=
  ⟨SSet.const x, by rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]⟩

/-- 概要：coslice の恒等錐の射影は元の頂点。
方針：定数射の Yoneda 表示を使う。
規約：恒等錐は x 下の coslice の頂点。
使われ方：HTT §1.2.12 の端点を固定した持ち上げの双対。 -/
lemma cosliceIdentityCone_projection {X : SSet.{u}} (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (cosliceIdentityCone x) = x := by
  change SSet.yonedaEquiv (_ ≫ SSet.const x) = x
  rw [SSet.comp_const, SSet.yonedaEquiv_const]

/-- 概要：始対象に入る任意の辺は、恒等辺への合成二単体を持つ片側の逆射を持つ。
方針：終点で恒等錐を固定して coslice 射影に沿い辺を持ち上げ、点と辺の join を三角形に直す。
規約：quasicategory 性はこの構成には不要。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の二つの始対象の同型。 -/
lemma IsInitialVertex.nonempty_split {X : SSet.{u}} {x y : X _⦋0⦌}
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y) (f : Edge (X := (truncation 2).obj X) x y) :
    Nonempty (Σ g : Edge (X := (truncation 2).obj X) y x,
      SSet.Truncated.Edge.CompStruct g f
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y)) := by
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration y).1 hy
  let a := SSet.yonedaEquiv.symm (cosliceIdentityCone y)
  let b : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm f.edge
  have := ht.mem (stdSimplex.δ (0 : Fin 2)) inferInstance
  have sq : CommSq a (stdSimplex.δ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm y)) b := by
    constructor
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, cosliceIdentityCone_projection,
      stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [b]
    rw [Equiv.apply_symm_apply]
    exact f.tgt_eq.symm
  let c := sq.lift
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry c
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ L
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ F = b := by
    dsimp [F]
    rw [← joinStdSimplexIso_one_inr, Category.assoc, Iso.hom_inv_id_assoc]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection c).trans sq.fac_right
  have hv (i : Fin 2) : stdSimplex.δ i.succ ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ i) ≫ L) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← joinStdSimplexIso_vertex_one, Category.assoc]
    dsimp [F]
    rw [Iso.hom_inv_id_assoc]
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ F = SSet.const y := by
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry sq.fac_left
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, sliceUnderUncurry_yoneda] at he
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, hv, he]
    exact SSet.comp_const _ y
  let z := SSet.yonedaEquiv F
  have hz₀ : X.δ (0 : Fin 3) z = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₀]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have hz₁ : X.δ (1 : Fin 3) z = (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₁]
    change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op y =
      X.map (SimplexCategory.σ (0 : Fin 1)).op y
    exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ ↦ X.map α.op y) (by decide)
  have hsrc : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) z) = y := by
    have he : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) z) =
        X.δ (1 : Fin 2) (X.δ (1 : Fin 3) z) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op z)
      decide
    rw [he, hz₁]
    exact (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y).src_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) z) = x := by
    have he : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) z) =
        X.δ (1 : Fin 2) (X.δ (0 : Fin 3) z) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op z)
      decide
    rw [he, hz₀]
    exact f.src_eq
  let g : Edge (X := (truncation 2).obj X) y x := ⟨X.δ 2 z, hsrc, htgt⟩
  exact ⟨⟨g, ⟨z, rfl, hz₀, hz₁⟩⟩⟩

/-- 概要：二つの始対象となる頂点は辺のホモトピー類による圏で同型。
方針：片側逆射を二回作り、合成関係から両側逆射に直す。
規約：X は Mathlib の quasicategory。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の始対象の一意性。 -/
noncomputable def initialVertexIso₂ {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y) :
    HomotopyCategory₂.mk (A := (truncation 2).obj X) x ≅ HomotopyCategory₂.mk y := by
  let f := Classical.choice (hx.nonempty_edge y)
  let sg := Classical.choice (hy.nonempty_split f)
  let g := sg.1
  let sk := Classical.choice (hx.nonempty_split g)
  let k := sk.1
  have hg : HomotopyCategory₂.homMk g ≫ HomotopyCategory₂.homMk f =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) y) := sg.2.homotopyCategory₂_fac
  have hk : HomotopyCategory₂.homMk k ≫ HomotopyCategory₂.homMk g =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) x) := sk.2.homotopyCategory₂_fac
  have hf : HomotopyCategory₂.homMk f = HomotopyCategory₂.homMk k := by
    calc
      _ = (HomotopyCategory₂.homMk k ≫ HomotopyCategory₂.homMk g) ≫
          HomotopyCategory₂.homMk f := by rw [hk, Category.id_comp]
      _ = HomotopyCategory₂.homMk k ≫ (HomotopyCategory₂.homMk g ≫
          HomotopyCategory₂.homMk f) := Category.assoc _ _ _
      _ = HomotopyCategory₂.homMk k := by rw [hg, Category.comp_id]
  exact ⟨HomotopyCategory₂.homMk f, HomotopyCategory₂.homMk g, by rw [hf]; exact hk, hg⟩

/-- 概要：二つの始対象となる頂点は Mathlib のホモトピー圏 hX で同型。
方針：辺の商の同型を A1 の比較同値で写す。
規約：X は Mathlib の quasicategory。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の始対象の一意性。 -/
noncomputable def initialVertexIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y) :
    (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ≅ SSet.HomotopyCategory.mk y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).functor.mapIso (initialVertexIso₂ hx hy)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
