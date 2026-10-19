module
public import SerrePositivity.KST.SConstruction.FiberResolutionCanonical

/-! # fiber 解消の標準因子分解からの一意な射
概要：各対象 e に対し、その元の X 単体の標準因子分解から一意な射を構成する。
方針：対象のパラメーターを底の単体の射とし、二射影でラベル条件を確認する。
規約：選んだ単体の射そのものの一意性。使われ方：反対圏における augmentation の縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：標準因子分解から元の対象へ向かう底の単体圏の射。
方針：元の因子分解のパラメーターと f の可換条件を使う。
規約：元の標準単体の射をそのまま使う。使われ方：要素の圏での標準射。 -/
def fiberResolutionCanonicalBaseArrow {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) :
    (fiberResolutionCanonical f (fiberResolutionValue f e)).obj ⟶ e.obj :=
  (Functor.Elements.homMk (stdSimplex.objEquiv (fiberResolutionParameter f e)).op
    (fiberResolution_condition f e).symm).op

/-- 概要：底の標準射による係数の輸送は元の左 fiber の単体を厳密に回収する。
方針：左 fiber の単体の二射影で等号を確認する。
規約：元の単体のラベルの等号。使われ方：標準因子分解射の構成。 -/
lemma fiberResolutionCanonicalBaseArrow_map {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) :
    (fiberResolutionCoefficient f n).map (fiberResolutionCanonicalBaseArrow f e)
      (fiberResolutionCanonical f (fiberResolutionValue f e)).val = e.val := by
  apply (simplexLeftFiberSimplexEquiv f e.obj.unop.val n).injective
  apply Subtype.ext
  apply Prod.ext
  · have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
      (simplexFiberDiagramMap_projection f (fiberResolutionCanonicalBaseArrow f e))
        (Opposite.op ⦋n⦌)) (fiberResolutionCanonicalSimplex f (fiberResolutionValue f e))
    change (simplexLeftFiberProjection f e.obj.unop.val).app (Opposite.op ⦋n⦌)
        ((fiberResolutionCoefficient f n).map (fiberResolutionCanonicalBaseArrow f e)
          (fiberResolutionCanonical f (fiberResolutionValue f e)).val) =
      (simplexLeftFiberProjection f (f.app (Opposite.op ⦋n⦌) (fiberResolutionValue f e))).app
        (Opposite.op ⦋n⦌) (fiberResolutionCanonicalSimplex f (fiberResolutionValue f e)) at hp
    rw [fiberResolutionCanonicalSimplex_projection] at hp
    exact hp
  · have hp := ConcreteCategory.congr_hom (NatTrans.congr_app
      (simplexFiberDiagramMap_parameter f (fiberResolutionCanonicalBaseArrow f e))
        (Opposite.op ⦋n⦌)) (fiberResolutionCanonicalSimplex f (fiberResolutionValue f e))
    change (simplexLeftFiberParameter f e.obj.unop.val).app (Opposite.op ⦋n⦌)
        ((fiberResolutionCoefficient f n).map (fiberResolutionCanonicalBaseArrow f e)
          (fiberResolutionCanonical f (fiberResolutionValue f e)).val) =
      (stdSimplex.map (stdSimplex.objEquiv (fiberResolutionParameter f e))).app (Opposite.op ⦋n⦌)
        ((simplexLeftFiberParameter f (f.app (Opposite.op ⦋n⦌) (fiberResolutionValue f e))).app
          (Opposite.op ⦋n⦌) (fiberResolutionCanonicalSimplex f (fiberResolutionValue f e))) at hp
    rw [fiberResolutionCanonicalSimplex_parameter, ← SSet.yonedaEquiv_comp,
      Category.id_comp, SSet.yonedaEquiv_map, Equiv.symm_apply_apply] at hp
    exact hp

/-- 概要：各因子分解対象へ向かう標準因子分解射。
方針：底の標準射とそのラベルの輸送の等号を要素の圏の射にする。
規約：任意の新しい射の選択はない。使われ方：縮約の自然変換の成分。 -/
def fiberResolutionCanonicalArrow {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (e : fiberResolutionCategory f n) :
    fiberResolutionCanonical f (fiberResolutionValue f e) ⟶ e :=
  Functor.Elements.homMk (fiberResolutionCanonicalBaseArrow f e)
    (fiberResolutionCanonicalBaseArrow_map f e)

/-- 概要：標準因子分解を始域とする任意の二つの因子分解射は等しい。
方針：恒等パラメーターの輸送が終域のパラメーターを決めるので底の射も一意。
規約：単体の射の等号まで証明する。使われ方：縮約の自然性。 -/
lemma fiberResolutionCanonicalArrow_unique {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : X _⦋n⦌) (e : fiberResolutionCategory f n)
    (h k : fiberResolutionCanonical f x ⟶ e) : h = k := by
  have hh := fiberResolutionParameter_map f h
  have hk := fiberResolutionParameter_map f k
  rw [fiberResolutionCanonical_parameter] at hh hk
  let θh : ⦋n⦌ ⟶ e.obj.unop.obj.unop := h.hom.unop.hom.unop
  let θk : ⦋n⦌ ⟶ e.obj.unop.obj.unop := k.hom.unop.hom.unop
  change fiberResolutionParameter f e =
    (stdSimplex.map θh).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u}))) at hh
  change fiberResolutionParameter f e =
    (stdSimplex.map θk).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u}))) at hk
  rw [← SSet.yonedaEquiv_comp, Category.id_comp, SSet.yonedaEquiv_map] at hh hk
  have he : h.hom.unop.hom.unop = k.hom.unop.hom.unop :=
    stdSimplex.objEquiv.symm.injective (hh.symm.trans hk)
  apply Functor.Elements.hom_ext
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  exact Quiver.Hom.unop_inj he

end SerrePositivity.KST.SConstruction
