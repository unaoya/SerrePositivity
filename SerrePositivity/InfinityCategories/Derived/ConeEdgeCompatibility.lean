module
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! # 錐の比較辺と指定された脚の整合

概要：slice の辺を射影した比較辺と二つの錐の脚は三角形で可換である。
方針：比較辺を uncurry し、図式の一頂点へ制限して二単体を得る。
規約：図式の頂点と脚を固定する。使われ方：D6a の四辺と長完全列の射の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial

/-- 概要：join 錐の指定した図式の頂点への脚。
方針：図式をその一頂点へ制限し、二点の join を一単体として読む。
規約：始点は錐の頂点、終点は図式の指定頂点。使われ方：四角形の二つの脚。 -/
def derivedConeLeg {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) (v : K _⦋0⦌) :
    Edge (X := (truncation 2).obj X) c.vertex (p.app _ v) where
  edge := SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm v) ≫ c.val)
  src_eq := by
    change X.δ 1 (SSet.yonedaEquiv _) = c.vertex
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← joinStdSimplexIso_zero_inl,
      Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, joinInl_joinMap,
      Category.id_comp]
    exact c.vertex_eq.symm
  tgt_eq := by
    change X.δ 0 (SSet.yonedaEquiv _) = p.app _ v
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← joinStdSimplexIso_zero_inr,
      Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, joinInr_joinMap,
      Category.assoc, c.property, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：錐の比較辺は各指定脚と三角形で両立する。
方針：slice の一単体を一頂点に制限した join の二単体の三面を評価する。
規約：三角形の最初の辺は頂点の比較、最後の辺は比較先の脚。使われ方：Hⁱ の射の整合。 -/
def derivedConeLegCompStruct {K X : SSet.{u}} {p : K ⟶ X} {c d : JoinCone p}
    (e : Edge (X := (truncation 2).obj (sliceOver p)) c d) (v : K _⦋0⦌) :
    SSet.Truncated.Edge.CompStruct (e.map ((truncation 2).map (sliceOverProjection p)))
      (derivedConeLeg d v) (derivedConeLeg c v) := by
  let L := sliceOverUncurry (SSet.yonedaEquiv.symm e.edge)
  let γ : (Δ[0] : SSet.{u}) ⟶ K := SSet.yonedaEquiv.symm v
  let F := (joinStdSimplexIso 1 0).inv ≫ joinMap (𝟙 Δ[1]) γ ≫ L
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ F =
      SSet.yonedaEquiv.symm (e.map ((truncation 2).map (sliceOverProjection p))).edge := by
    dsimp only [F]
    rw [← joinStdSimplexIso_one_inl, Category.assoc, Iso.hom_inv_id_assoc,
      ← Category.assoc, joinInl_joinMap, Category.id_comp]
    rw [sliceOverUncurry_projection, SSet.yonedaEquiv_symm_comp]
    rfl
  have hv (i : Fin 2) : stdSimplex.δ i.castSucc ≫ F =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) γ ≫
        (sliceOverUncurry (stdSimplex.δ i ≫ SSet.yonedaEquiv.symm e.edge)) := by
    apply (cancel_epi (joinStdSimplexIso 0 0).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← joinStdSimplexIso_one_vertex]
    dsimp only [F]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [sliceOverUncurry_precomp]
    simp only [← Category.assoc, ← joinMap_comp, Category.comp_id, Category.id_comp]
    rfl
  have he (i : Fin 2) : stdSimplex.δ i.castSucc ≫ F =
      (joinStdSimplexIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) γ ≫
        (((sliceOver p).δ i e.edge) : JoinCone p).val := by
    rw [hv, stdSimplex.δ_comp_yonedaEquiv_symm, sliceOverUncurry_yoneda]
  have hs : (sliceOver p).δ 1 e.edge = c := e.src_eq
  have ht : (sliceOver p).δ 0 e.edge = d := e.tgt_eq
  refine ⟨SSet.yonedaEquiv F, ?_, ?_, ?_⟩
  · change X.δ 2 (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₂]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · change X.δ 0 (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, show (0 : Fin 3) = (0 : Fin 2).castSucc from rfl,
      he, ht]
    rfl
  · change X.δ 1 (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, show (1 : Fin 3) = (1 : Fin 2).castSucc from rfl,
      he, hs]
    rfl

/-- 概要：錐の比較辺と指定した脚の合成はホモトピー圏で元の脚になる。
方針：直前の比較三角形の合成関係を使う。
規約：X は quasicategory。使われ方：導来圏とホモロジーへ移す等式。 -/
lemma derivedConeLeg_homMk_comp {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (e : Edge (X := (truncation 2).obj (sliceOver p)) c d)
    (v : K _⦋0⦌) :
    HomotopyCategory₂.homMk (e.map ((truncation 2).map (sliceOverProjection p))) ≫
      HomotopyCategory₂.homMk (derivedConeLeg d v) = HomotopyCategory₂.homMk (derivedConeLeg c v) :=
  (derivedConeLegCompStruct e v).homotopyCategory₂_fac

end SerrePositivity.InfinityCategories
