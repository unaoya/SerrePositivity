module

public import SerrePositivity.InfinityCategories.F1.Categories.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyOppositeLaws
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRightHom
public import SerrePositivity.InfinityCategories.Core.MappingSpaceLeft

/-!
概要：関手単体集合の反転同型による h Fun の逆向き Hom 対応。
方針：ホモトピー圏の反転 Hom 全単射と内部 Hom の反転同型を合成する。
規約：指定された二胞体と実際のホモトピー代表の反転を一致させる。
使われ方：左 Kan の Hom 普遍性を右側へ双対化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：ホモトピー圏の反転 Hom 全単射は辺の類を反転した辺の類へ送る。
方針：辺の商によるホモトピー圏の比較とその逆を消す。
規約：straightening に依存しない Core の比較だけを使う。
使われ方：指定ホモトピーの類と反転 Hom 全単射の一致。 -/
lemma kanHomotopyCategoryOpHomEquiv_homMk {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    homotopyCategoryOpHomEquiv x y (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory.homMk (edgeOp e) := by
  let a := (homotopyCategoryBridge X).fullyFaithfulFunctor.homEquiv
    (X := SSet.Truncated.HomotopyCategory₂.mk (A := (truncation 2).obj X) x)
    (Y := SSet.Truncated.HomotopyCategory₂.mk (A := (truncation 2).obj X) y)
  let b := (homotopyCategoryBridge X.op).fullyFaithfulFunctor.homEquiv
    (X := SSet.Truncated.HomotopyCategory₂.mk (A := (truncation 2).obj X.op)
      (SSet.opObjEquiv.symm y))
    (Y := SSet.Truncated.HomotopyCategory₂.mk (A := (truncation 2).obj X.op)
      (SSet.opObjEquiv.symm x))
  exact congrArg (fun t ↦ b (homotopyCategory₂OpHomEquiv x y t))
    (a.symm_apply_apply (SSet.Truncated.HomotopyCategory₂.homMk e))

/-- 概要：内部 Hom の反転同型の各成分は単体の順序と係数を反転する。
方針：指数比較の評価公式を単体に適用し、比較の自然性でパラメータを移す。
規約：標準単体の任意の次数のパラメータを扱う。
使われ方：反転した関手頂点とホモトピーの辺の同定。 -/
lemma kanOppositeInternalHom_apply {A D : SSet.{u}} {n m : SimplexCategoryᵒᵖ}
    (s : ((ihom A).obj D).op.obj n) (α : n ⟶ m) (a : A.op.obj m) :
    ((HomotopyLimits.oppositeInternalHomIso A D).hom.app n s).app m α a =
      SSet.opObjEquiv.symm ((SSet.opObjEquiv s).app m
        (SimplexCategory.rev.op.map α) (SSet.opObjEquiv a)) := by
  let q := (HomotopyLimits.oppositeInternalHomIso A D).hom
  let z : (A.op ⊗ ((ihom A).obj D).op).obj m :=
    ⟨a, (((ihom A).obj D).op).map α s⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (oppositeInternalHomIso_uncurry A D) m) z
  have hn := q.naturality_apply α s
  change (q.app m ((((ihom A).obj D).op).map α s)).app m (𝟙 m) a = _ at h
  rw [hn] at h
  exact h

/-- 概要：内部 Hom の反転同型は関手頂点を元の関手の反転へ送る。
方針：指数比較の頂点を各次数で評価する。
規約：quasicategory 性は不要。
使われ方：反転した Hom の両端の同定。 -/
lemma kanOppositeInternalHom_vertex {A D : SSet.{u}} (F : A ⟶ D) :
    (HomotopyLimits.oppositeInternalHomIso A D).hom.app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (functorVertex F)) = functorVertex (SSet.opFunctor.map F) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro a
  rw [kanOppositeInternalHom_apply]
  rfl

/-- 概要：内部 Hom の反転同型は指定ホモトピーの辺をその反転の辺へ送る。
方針：各次数の式でパラメータと係数の反転を計算する。
規約：代表の類だけでなく一次単体が一致する。
使われ方：Hom 反転全単射と実際の指定変換の反転の照合。 -/
lemma kanOppositeInternalHom_homotopy_edge {A D : SSet.{u}} {F G : A ⟶ D}
    (H : SSet.Homotopy F G) :
    (HomotopyLimits.oppositeInternalHomIso A D).hom.app (Opposite.op ⦋1⦌)
        (SSet.opObjEquiv.symm (functorEdgeOfSimplicialHomotopy H).edge) =
      (functorEdgeOfSimplicialHomotopy (kanHomotopyOpposite H)).edge := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro a
  rw [kanOppositeInternalHom_apply]
  rfl

/-- 概要：h Fun の Hom は両図式を反転した逆向きの Hom と全単射。
方針：ホモトピー圏の反転と内部 Hom の反転同型を合成し、関手頂点へ端点を輸送する。
規約：標的 D のみ quasicategory とする。
使われ方：指定右 Kan 変換の大域的 Hom 普遍性の双対化。 -/
def kanFunctorOppositeHomEquiv {A D : SSet.{u}} [Quasicategory D] (F G : A ⟶ D) :
    FunctorHom F G ≃ FunctorHom (SSet.opFunctor.map G) (SSet.opFunctor.map F) := by
  let q := HomotopyLimits.oppositeInternalHomIso A D
  let e :
      ((HomotopyCategory.mk (SSet.opObjEquiv.symm (functorVertex G)) :
        hoFunctor.obj ((ihom A).obj D).op) ⟶
          HomotopyCategory.mk (SSet.opObjEquiv.symm (functorVertex F))) ≃
      ((HomotopyCategory.mk (q.hom.app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (functorVertex G))) : hoFunctor.obj ((ihom A.op).obj D.op)) ⟶
        HomotopyCategory.mk (q.hom.app (Opposite.op ⦋0⦌)
          (SSet.opObjEquiv.symm (functorVertex F)))) :=
    Equiv.ofBijective (hoFunctor.map q.hom).toFunctor.map
      ((qCatEquivalenceOfIso q).isFullyFaithful.toHoFullyFaithful.map_bijective _ _)
  exact (homotopyCategoryOpHomEquiv (functorVertex F) (functorVertex G)).trans
    (e.trans (Iso.homCongr
      (eqToIso (congrArg HomotopyCategory.mk (kanOppositeInternalHom_vertex G)))
      (eqToIso (congrArg HomotopyCategory.mk (kanOppositeInternalHom_vertex F)))))

/-- 概要：Hom の反転全単射は指定ホモトピーの類をその反転の類へ送る。
方針：辺の反転の公式、内部 Hom の辺の計算、両端の輸送を合成する。
規約：元の指定ホモトピー H 自身を使う。
使われ方：右 Kan の指定変換と双対化後の指定変換の一致。 -/
lemma kanFunctorOppositeHomEquiv_homotopy {A D : SSet.{u}} [Quasicategory D]
    {F G : A ⟶ D} (H : SSet.Homotopy F G) :
    kanFunctorOppositeHomEquiv F G
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanHomotopyOpposite H)) := by
  simp only [kanFunctorOppositeHomEquiv, Equiv.trans_apply,
    kanHomotopyCategoryOpHomEquiv_homMk,
    Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  apply homMk_transport (kanOppositeInternalHom_vertex G) (kanOppositeInternalHom_vertex F)
  exact kanOppositeInternalHom_homotopy_edge H

/-- 概要：ホモトピー圏の反転 Hom 全単射は合成の順序を交換する。
方針：両射を辺で表し、合成を表す二単体を反転する。
規約：quasicategory の任意の三頂点を扱う。
使われ方：関手の二胞体の反転と縦合成の両立。 -/
lemma kanHomotopyCategoryOpHomEquiv_comp {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y)
    (β : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk z) :
    homotopyCategoryOpHomEquiv x z (α ≫ β) =
      homotopyCategoryOpHomEquiv y z β ≫ homotopyCategoryOpHomEquiv x y α := by
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective x y α
  obtain ⟨f, rfl⟩ := homotopyCategory_homMk_surjective y z β
  rw [SSet.Truncated.HomotopyCategory.homMk_comp_homMk (SSet.Truncated.Edge.compStruct e f)]
  rw [kanHomotopyCategoryOpHomEquiv_homMk, kanHomotopyCategoryOpHomEquiv_homMk,
    kanHomotopyCategoryOpHomEquiv_homMk]
  exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (compStructOp (SSet.Truncated.Edge.compStruct e f))).symm

/-- 概要：関手の二胞体の反転は縦合成の順序を交換する。
方針：ホモトピー圏の反転の合成公式を内部 Hom の同型で写し、端点の輸送を相殺する。
規約：可逆でない二胞体にも成立する。
使われ方：右 Kan の比較写像を左 Kan の比較写像へ移す。 -/
lemma kanFunctorOppositeHomEquiv_comp {A D : SSet.{u}} [Quasicategory D]
    {F G H : A ⟶ D} (α : FunctorHom F G) (β : FunctorHom G H) :
    kanFunctorOppositeHomEquiv F H (α ≫ β) =
      kanFunctorOppositeHomEquiv G H β ≫ kanFunctorOppositeHomEquiv F G α := by
  simp only [kanFunctorOppositeHomEquiv, Equiv.trans_apply,
    kanHomotopyCategoryOpHomEquiv_comp, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    Equiv.coe_ofBijective, CategoryTheory.Functor.map_comp,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- 概要：関手の二胞体の反転は始域での前合成に両立する。
方針：指定射のホモトピー代表を取り、反転と前合成の raw な等式を類へ移す。
規約：始域に quasicategory 性を要求しない。
使われ方：Kan の底関手 δ による制限の反転。 -/
lemma kanFunctorOppositeHomEquiv_precomp {A B D : SSet.{u}} [Quasicategory D]
    (i : A ⟶ B) {F G : B ⟶ D} (α : FunctorHom F G) :
    kanFunctorOppositeHomEquiv (i ≫ F) (i ≫ G)
        ((hoFunctor.map ((pre i).app D)).toFunctor.map α) =
      (hoFunctor.map ((pre (SSet.opFunctor.map i)).app D.op)).toFunctor.map
        (kanFunctorOppositeHomEquiv F G α) := by
  have h := functorHomHomotopy_hom α
  rw [← h, ← functorHomotopyPrecomp_hom, kanFunctorOppositeHomEquiv_homotopy,
    kanFunctorOppositeHomEquiv_homotopy, ← functorHomotopyPrecomp_hom]
  congr 1

end SerrePositivity.InfinityCategories.F1B
