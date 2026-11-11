module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationInitialPiZeroNaturality

/-! # 始対象による Hom 表示の自然性

概要：始対象を持つ left fibration の fiber の Hom 表示は底上の関手に自然。
方針：coslice 表示の自然性を左写像空間へ移し、始点の等号を Hom の前合成で表す。
規約：始点の像の等号による輸送を明示する。使われ方：余錐の制限と二枝交換の Hom への作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：等しい点図式の coslice と左写像空間の比較は始点の等号の輸送と可換。
方針：点図式と始点の等号の帰納法で恒等の場合に戻す。
規約：空間の射の厳密な等号。使われ方：Hom 表示の自然性の模型変更。 -/
lemma stablePinchedLeftBaseIso_transport {B : SSet.{u}} {a b : (Δ[0] : SSet.{u}) ⟶ B}
    {x z : B _⦋0⦌} (ha : a = SSet.yonedaEquiv.symm x)
    (hb : b = SSet.yonedaEquiv.symm z) (h : a = b) (hx : x = z) (y : B _⦋0⦌) :
    eqToHom (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y) h) ≫
      (eqToIso (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y) hb) ≪≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso z y).symm).hom =
    (eqToIso (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection t) y) ha) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso x y).symm).hom ≫
        eqToHom (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) hx) := by
  subst z
  subst a
  subst b
  simp only [eqToHom_refl, eqToIso_refl, Iso.refl_trans, Category.id_comp, Category.comp_id]

/-- 概要：左写像空間の連結成分から Hom への同値は始点の等号輸送と可換。
方針：始点の等号を消す。
規約：Hom の始点は反変に移る。使われ方：模型の自然性をホモトピー圏へ移す。 -/
lemma stablePinchedHomLeftPiZeroEquiv_transport {B : SSet.{u}} [Quasicategory B]
    {x z : B _⦋0⦌} (hx : x = z) (y : B _⦋0⦌) (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv z y
      (SSet.mapπ₀ (eqToHom (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) hx)) a) =
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj B)) hx.symm) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv x y a := by
  subst z
  simp only [eqToHom_refl, SSet.mapπ₀_id_apply, Category.id_comp]

/-- 概要：底上の関手が保つ始点の底への像は等しい。
方針：底への合成の等号を始点で評価する。
規約：関手による像の始点の等号を明示する。使われ方：Hom の始点の輸送。 -/
lemma leftFibrationInitialImage_eq {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) (c : E _⦋0⦌) (d : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) c = d) :
    p.app (Opposite.op ⦋0⦌) c = q.app (Opposite.op ⦋0⦌) d := by
  rw [← hd]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hf (Opposite.op ⦋0⦌)) c).symm

/-- 概要：始対象からの fiber の Hom 表示は同じ底上の関手に自然。
方針：比較 span の π₀ の自然性を左模型へ移し、始点の輸送を前合成へ変換する。
規約：始点とその像の両方の始対象性を要求する。使われ方：余錐の制限と二枝交換の Hom 比較。 -/
lemma leftFibrationInitialFiberPiZeroEquiv_naturality
    {E F B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] (f : E ⟶ F) (hf : f ≫ q = p)
    (c : E _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex c) (d : F _⦋0⦌) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex d)
    (hcd : f.app (Opposite.op ⦋0⦌) c = d) (y : B _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y)) :
    eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj B))
      (leftFibrationInitialImage_eq p q f hf c d hcd)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv q d hd y (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf y) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv p c hc y a := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberCoslicePiZeroEquiv_naturality p q f hf c hc d hd hcd y a
  have hb := stablePinchedLeftBaseIso_transport (SSet.yonedaEquiv_symm_comp d q)
    (SSet.yonedaEquiv_symm_comp c p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseDiagram_eq p q f hf c d hcd).symm
    (leftFibrationInitialImage_eq p q f hf c d hcd).symm y
  change eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p c y).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso q d y).hom ≫ eqToHom _ at hb
  have hh := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv (p.app (Opposite.op ⦋0⦌) c) y
    (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso p c y).hom t)) h
  rw [← SSet.mapπ₀_comp_apply, hb, SSet.mapπ₀_comp_apply,
    stablePinchedHomLeftPiZeroEquiv_transport
      (leftFibrationInitialImage_eq p q f hf c d hcd).symm] at hh
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.leftFibrationInitialFiberPiZeroEquiv_eq_coslice] using hh

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
