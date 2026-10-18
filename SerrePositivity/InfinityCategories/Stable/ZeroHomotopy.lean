module
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-! # ホモトピー圏の零対象

概要：始頂点と終頂点は h C でも始対象と終対象となる。
方針：始頂点の coslice 射影の可縮な fiber で平行辺を比較する。
規約：h C は Mathlib の hoFunctor。使われ方：S3 の Σ・Ω と零射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet SSet.Truncated SimplicialObject.Truncated
open scoped Simplicial

/-- 概要：辺はその始点の coslice の頂点を与える。
方針：二点の join を標準辺と同定する。
規約：射影は元の辺の終点。使われ方：始対象から出る辺の比較。 -/
def edgeCosliceVertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : Edge (X := (truncation 2).obj X) x y) :
    (sliceUnder (SSet.yonedaEquiv.symm x)) _⦋0⦌ :=
  ⟨(joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge, by
    rw [← Category.assoc, joinStdSimplexIso_zero_inl]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact f.src_eq⟩

/-- 概要：辺の coslice 頂点の射影は終点である。
方針：右包含の面を計算する。
規約：厳密な頂点の等式。使われ方：同じ終点を持つ辺を fiber に入れる。 -/
lemma edgeCosliceVertex_projection {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : Edge (X := (truncation 2).obj X) x y) :
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (edgeCosliceVertex f) = y := by
  change SSet.yonedaEquiv (joinInr Δ[0] Δ[0] ≫
    ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge)) = _
  rw [← Category.assoc, joinStdSimplexIso_zero_inr,
    stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact f.tgt_eq

/-- 概要：始頂点から出る二つの平行辺は h₂ C で同じ射を表す。
方針：coslice 射影の同一 fiber の二頂点を結び、その二単体の合成関係を読む。
規約：元の C は quasicategory。使われ方：始頂点が h C の始対象となること。 -/
lemma IsInitialVertex.homMk_eq {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (hx : IsInitialVertex x) (f g : Edge (X := (truncation 2).obj X) x y) :
    HomotopyCategory₂.homMk f = HomotopyCategory₂.homMk g := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have : TrivialKanFibration p := (isInitialVertex_iff_trivialKanFibration x).1 hx
  let v (a : Edge (X := (truncation 2).obj X) x y) : (vertexFiber p y) _⦋0⦌ :=
    ⟨edgeCosliceVertex a, by rw [pinchedConstant_zero]; exact edgeCosliceVertex_projection a⟩
  have hc := vertexFiber_isContractibleKan p y
  let e := Classical.choice ((hc.isTerminalVertex (v g)).nonempty_edge (v f))
  let L := e.edge.val.val
  let F := (joinStdSimplexIso 0 1).inv ≫ L
  have hv (i : Fin 2) : stdSimplex.δ i.succ ≫ F =
      (joinStdSimplexIso 0 0).inv ≫ (joinMap (𝟙 Δ[0]) (stdSimplex.δ i) ≫ L) := by
    apply (cancel_epi (joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← joinStdSimplexIso_vertex_one, Category.assoc]
    dsimp [F]
    rw [Iso.hom_inv_id_assoc]
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ F = SSet.yonedaEquiv.symm f.edge := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl, hv]
    have he := congrArg (fun s : (vertexFiber p y) _⦋0⦌ => s.val.val) e.src_eq
    change joinMap (𝟙 Δ[0]) (stdSimplex.δ 1) ≫ L = (edgeCosliceVertex f).val at he
    rw [he]
    exact Iso.inv_hom_id_assoc _ _
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ F = SSet.yonedaEquiv.symm g.edge := by
    rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl, hv]
    have he := congrArg (fun s : (vertexFiber p y) _⦋0⦌ => s.val.val) e.tgt_eq
    change joinMap (𝟙 Δ[0]) (stdSimplex.δ 0) ≫ L = (edgeCosliceVertex g).val at he
    rw [he]
    exact Iso.inv_hom_id_assoc _ _
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ F = SSet.const y := by
    rw [← joinStdSimplexIso_one_inr, Category.assoc]
    dsimp only [F]
    rw [Iso.hom_inv_id_assoc]
    apply SSet.yonedaEquiv.injective
    exact e.edge.property
  have t : SSet.Truncated.Edge.CompStruct f (Edge.id (X := (truncation 2).obj X) y) g := by
    refine ⟨SSet.yonedaEquiv F, ?_, ?_, ?_⟩
    · change X.δ 2 (SSet.yonedaEquiv F) = f.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₂]
      exact (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply f.edge
    · change X.δ 0 (SSet.yonedaEquiv F) = X.σ 0 y
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₀]
      change X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op y =
        X.map (SimplexCategory.σ (0 : Fin 1)).op y
      exact congrArg (fun α : ⦋1⦌ ⟶ ⦋0⦌ => X.map α.op y) (by decide)
    · change X.δ 1 (SSet.yonedaEquiv F) = g.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₁]
      exact (SSet.yonedaEquiv (X := X) (n := ⦋1⦌)).apply_symm_apply g.edge
  have ht := t.homotopyCategory₂_fac
  change HomotopyCategory₂.homMk f ≫ 𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) y) =
    HomotopyCategory₂.homMk g at ht
  simpa using ht

/-- 概要：始頂点は辺のホモトピー類の圏でも始対象である。
方針：辺の存在と平行辺の類の一致を商へ降ろす。
規約：二切断の h₂ C。使われ方：Mathlib の h C への移送。 -/
def IsInitialVertex.isInitialHo₂ {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌}
    (hx : IsInitialVertex x) :
    IsInitial (HomotopyCategory₂.mk (A := (truncation 2).obj X) x) := by
  have h (z : HomotopyCategory₂ ((truncation 2).obj X)) :
      Unique (HomotopyCategory₂.mk x ⟶ z) := by
    refine ⟨⟨HomotopyCategory₂.homMk (Classical.choice (hx.nonempty_edge z.pt))⟩, ?_⟩
    intro a
    obtain ⟨a, rfl⟩ := HomotopyCategory₂.homMk_surjective a
    exact hx.homMk_eq _ _
  exact IsInitial.ofUnique _

/-- 概要：始頂点は Mathlib の h C でも始対象である。
方針：辺のホモトピー類の圏との比較同値で始対象を写す。
規約：C の quasicategory 性を仮定する。使われ方：零頂点の零対象性。 -/
def IsInitialVertex.isInitialHo {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌}
    (hx : IsInitialVertex x) :
    IsInitial (SSet.HomotopyCategory.mk x : hoFunctor.obj X) :=
  hx.isInitialHo₂.isInitialObj (homotopyCategoryBridge X).functor _

/-- 概要：零頂点は h C の零対象を与える。
方針：始頂点・終頂点から h C の射の存在と一意性を使う。
規約：同じ頂点が始対象かつ終対象。使われ方：零射と suspension/loop の構成。 -/
lemma IsZeroVertex.isZeroHo {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌}
    (hx : IsZeroVertex x) : IsZero (SSet.HomotopyCategory.mk x : hoFunctor.obj X) where
  unique_to y := ⟨⟨⟨hx.1.isInitialHo.to y⟩, fun f => hx.1.isInitialHo.hom_ext f _⟩⟩
  unique_from y := ⟨⟨⟨hx.2.isTerminalHo.from y⟩, fun f => hx.2.isTerminalHo.hom_ext f _⟩⟩

/-- 概要：零頂点を持つ quasicategory のホモトピー圏は零対象を持つ。
方針：選んだ零頂点を h C に写す。
規約：安定性は不要。使われ方：h C の零射と三角構造の前提。 -/
instance hasZeroObject_ho {X : SSet.{u}} [Quasicategory X] [HasZeroVertex X] :
    HasZeroObject (hoFunctor.obj X) where
  zero := ⟨SSet.HomotopyCategory.mk (chosenZeroVertex X).vertex,
    (chosenZeroVertex X).isZero.isZeroHo⟩

end SerrePositivity.InfinityCategories

