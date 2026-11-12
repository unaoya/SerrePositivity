module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionSimplex

/-!
# 解像の旗での Hom 評価の単体的自然性

概要：pinched 単体の旗での評価は、全ての面・退化と可換な解像からの単体集合の射を与える。
方針：引き戻した Path を先頭部分と末尾に分解し、定値先頭面の単位で前半を消す。
規約：新しい始点が元の始点と異なる面も含む。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の解像を介する写像空間の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：解像の旗での評価は全ての単調写像による引き戻しと可換である。
方針：Path の前半と末尾への分解、豊穣合成保存、前半の単位への評価を使う。
規約：先頭の頂点を変える写像と退化も含む。
使われ方：Kerodon 2.5.9（Tag 00SC） の解像上の評価を単体集合の射にまとめる。 -/
lemma resolutionHomValue_pullback {x y : ClosedCategory R D} {n d e : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue s F) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue s (F.pullback α) := by
  let a : SimplicialThickening (ULift.{u} (Fin (n + 2))) := .mk (ULift.up F.start.castSucc)
  let b : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (F.maxAt (α 0)).castSucc)
  let c : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
    .mk (ULift.up (Fin.last (n + 1)))
  let P : (a ⟶[SSet] b) _⦋e⦌ :=
    (nerveMap (SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
      (.mk (ULift.up F.start)) (.mk (ULift.up (F.maxAt (α 0)))))).app (Opposite.op ⦋e⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagFrontFunctor F α)
  let Q : (b ⟶[SSet] c) _⦋e⦌ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor (F.pullback α)
  let T : (a ⟶[SSet] c) _⦋e⦌ := α.monotone.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F
  let φ : (a ⟶[SSet] c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y :=
    s.val.map a c ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s F.start) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_target_obj s))
  have hcomp : (eComp SSet a b c).app (Opposite.op ⦋e⦌) (P, Q) = T := by
    refine CategoryTheory.Functor.ext (fun t ↦ ?_)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath_decomposition F α t
  have hT : (a ⟶[SSet] c).map (SimplexCategory.mkHom α).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F) = T := by
    refine CategoryTheory.Functor.ext (fun t ↦ rfl)
  have hnat : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue s F) = φ.app (Opposite.op ⦋e⦌) T := by
    calc
      _ = φ.app (Opposite.op ⦋e⦌) ((a ⟶[SSet] c).map (SimplexCategory.mkHom α).op
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F)) :=
        (φ.naturality_apply (SimplexCategory.mkHom α).op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPathFunctor F)).symm
      _ = _ := congrArg (φ.app (Opposite.op ⦋e⦌)) hT
  have hfront : (s.val.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s F.start) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s (F.maxAt (α 0))))).app
        (Opposite.op ⦋e⦌) P = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) (D := D) x e :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_front_value s F.start (F.maxAt (α 0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagFrontFunctor F α)
  have hc : φ.app (Opposite.op ⦋e⦌) ((eComp SSet a b c).app _ (P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue s (F.pullback α))
        ((s.val.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s F.start)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s (F.maxAt (α 0))))).app (Opposite.op ⦋e⦌) P) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedHomValue_comp s.val a b c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s F.start)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_source_obj s (F.maxAt (α 0))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinched_target_obj s) P Q
  rw [hfront, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_right] at hc
  exact hnat.trans ((congrArg (φ.app (Opposite.op ⦋e⦌)) hcomp).symm.trans hc)

/-- 概要：coherent pinched 単体は補助解像から標準 Hom への実際の単体集合の射を与える。
方針：各旗での評価を全次数でまとめ、引き戻しとの可換性を自然性に使う。
規約：解像の単体の ULift だけを忘れて評価する。
使われ方：HA 1.3.1.17 の反対側の合成のホモトピーを解像上で構成する入口。 -/
def resolutionHomMap {x y : ClosedCategory R D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y where
  app _ := ↾fun F ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue s F.down
  naturality := by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro F
    exact (resolutionHomValue_pullback s F.down α.unop.toOrderHom).symm

/-- 概要：標準 Hom から来る単体の解像上の射は最大元の射影を通る。
方針：全旗での既存の評価式と米田の単体の値を比較する。
規約：単体集合の射の等式であり、頂点での一致に限らない。
使われ方：Kerodon 2.5.9（Tag 00SC） の解像による比較と逆向きの射の合成。 -/
lemma resolutionHomMap_standard {x y : ClosedCategory R D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R (D := D) x y n) :
    resolutionHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardCoherentPinchedSimplex σ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n ≫ SSet.yonedaEquiv.symm σ := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomValue_standard σ F.down

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
