module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationNaturality
public import SerrePositivity.KST.Spectra.PointedHomotopy

/-!
概要：点つき射の基点上の fiber と点つき普遍性。
方針：L9b の実際の fiber に fiberPoint を基点として付ける。
規約：底の頂点は全空間の基点の像を使い、基点の移送を明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの段ごとの fiber。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：頂点の基点保存式から点つき射を構成する。
方針：終対象からの基点射を定数写像で表す。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7。fiber の基点保存の束ね直し。 -/
def pointedHomOfBasepoint {X Y : PointedSimplicialSet.{u}} (f : X.right ⟶ Y.right)
    (hf : f.app _ X.basepoint = Y.basepoint) : X ⟶ Y :=
  Under.homMk f (by
    have hx : SSet.const X.basepoint = X.hom :=
      (SSet.unitHomEquiv X.right).symm_apply_apply X.hom
    have hy : SSet.const Y.basepoint = Y.hom :=
      (SSet.unitHomEquiv Y.right).symm_apply_apply Y.hom
    rw [← hx, SSet.const_comp, hf, hy])

/-- 概要：点つき射の基点上の点つき fiber。
方針：実際の pullback と fiberPoint を使う。
規約：基礎対象は L9b の KanFiber そのもの。
使われ方：Goerss–Jardine I §7、BF 1978 §2。スペクトルの fiber の各段。 -/
def pointedFiber {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) : PointedSimplicialSet.{u} :=
  PointedSimplicialSet.ofVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint)

/-- 概要：点つき fiber から全空間への包含。
方針：fiberι の基点保存を fiberPoint の計算から得る。
規約：点つき射として構成する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber 列の最初の射。 -/
def pointedFiberι {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) : pointedFiber p ⟶ E :=
  pointedHomOfBasepoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _ E.basepoint)) (by
    have hb : (pointedFiber p).basepoint = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint :=
      PointedSimplicialSet.basepoint_ofVertex _ _
    exact (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right _).app _) hb).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p.right E.basepoint))

/-- 概要：Kan fibration の点つき fiber は Kan。
方針：L9b の引き戻しによる Kan 性を使う。
規約：底と全空間の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の Kan 列。 -/
instance pointedFiber_kanComplex {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p.right] : KanComplex (pointedFiber p).right :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p.right (p.right.app _ E.basepoint)))

/-- 概要：基点上に合成が定数となる点つき射を fiber へ持ち上げる。
方針：通常の fiberLift と、包含による頂点の検出を使う。
規約：定数値は p が全空間の基点に取る値。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の構造射の構成。 -/
def pointedFiberLift {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f : A ⟶ E)
    (hf : f.right ≫ p.right = SSet.const (p.right.app _ E.basepoint)) : A ⟶ pointedFiber p :=
  pointedHomOfBasepoint (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p.right _ f.right hf) (by
    have hb : (pointedFiber p).basepoint = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p.right E.basepoint :=
      PointedSimplicialSet.basepoint_ofVertex _ _
    apply Eq.trans _ hb.symm
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext p.right (p.right.app _ E.basepoint)
    have hl := congrArg (fun k : A.right ⟶ E.right ↦ k.app _ A.basepoint)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p.right _ f.right hf)
    exact hl.trans ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p.right E.basepoint).symm))

/-- 概要：点つき fiber への持ち上げを包含すると元の点つき射。
方針：通常の pullback の第一成分の計算を使う。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7、BF 1978 §2。構造射の可換条件。 -/
@[reassoc (attr := simp)]
theorem pointedFiberLift_ι {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f : A ⟶ E)
    (hf : f.right ≫ p.right = SSet.const (p.right.app _ E.basepoint)) :
    pointedFiberLift p f hf ≫ pointedFiberι p = f := by
  apply Under.UnderMorphism.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι p.right _ f.right hf

/-- 概要：fiber の包含と元の点つき射の合成は零射。
方針：通常の fiber の定数性と元の射の基点保存を使う。
規約：零射は点つき圏の零対象を経由する射。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の構造射の定義域。 -/
@[reassoc (attr := simp)]
theorem pointedFiberι_comp {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    pointedFiberι p ≫ p = 0 := by
  apply Under.UnderMorphism.ext
  change (pointedFiberι p).right ≫ p.right = (0 : pointedFiber p ⟶ B).right
  rw [PointedObject.zero_right]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp p.right (p.right.app _ E.basepoint)).trans
    ((congrArg (fun b ↦ SSet.const (X := (pointedFiber p).right) b)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const B _).symm)

/-- 概要：合成が零射となる点つき射を fiber へ持ち上げる。
方針：零射の基礎表示を基点の定数射へ直して既存の持ち上げを使う。
規約：点つき圏での厳密な零合成を条件とする。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber 列の構造射。 -/
def pointedFiberLiftOfZero {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f : A ⟶ E)
    (hf : f ≫ p = 0) : A ⟶ pointedFiber p :=
  pointedFiberLift p f (by
    have h := congrArg Under.Hom.right hf
    change f.right ≫ p.right = (0 : A ⟶ B).right at h
    rw [PointedObject.zero_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const] at h
    exact h.trans (congrArg (fun b ↦ (SSet.const (X := A.right) b))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p).symm))

/-- 概要：零合成から作った fiber の持ち上げは包含後に元の射となる。
方針：点つき fiberLift の計算を使う。
規約：条件の証明の選択に依存しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。構造射の可換性。 -/
@[reassoc (attr := simp)]
theorem pointedFiberLiftOfZero_ι {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f : A ⟶ E)
    (hf : f ≫ p = 0) : pointedFiberLiftOfZero p f hf ≫ pointedFiberι p = f :=
  pointedFiberLift_ι p f _

/-- 概要：点つき fiber への射は全空間への包含後の射で決まる。
方針：通常の fiber の射の一意性を使う。
規約：任意の点つき始域。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber 列の可換条件。 -/
theorem pointedFiber_hom_ext {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B)
    {f g : A ⟶ pointedFiber p} (h : f ≫ pointedFiberι p = g ≫ pointedFiberι p) : f = g := by
  apply Under.UnderMorphism.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p.right _
  exact congrArg Under.Hom.right h

end

end SerrePositivity.KST.Spectra
