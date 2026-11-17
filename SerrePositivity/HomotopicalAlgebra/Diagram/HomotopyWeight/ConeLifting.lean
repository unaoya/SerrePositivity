module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Generators
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction

/-!
# 射影 cofibrant 重みの錐空間の持ち上げ

概要：Hovey §5 の重み付き錐は各頂点の境界の右類と Kan fibration を保つ。
方針：二変数随伴で持ち上げを移し、重みの射影 cofibrancy を使う。
規約：単体集合の完全なモデル構造は仮定しない。
使われ方：一般 homotopy 極限の写像空間の不変性。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.PointwiseAdjunction _root_.SerrePositivity.DiagramModel.WeightedCones
open scoped _root_.SSet.modelCategoryQuillen

variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries K).rlp.llp (initial.to W))

include hW

private lemma tensor_map_lifting {X Y : SSet.{u}} (i : X ⟶ Y)
    {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    (h : ∀ k, ∀ {A B : SSet.{u}} (j : A ⟶ B), SSet.modelCategoryQuillen.I j →
      ∀ sq : (curriedTensor SSet.{u}).PushoutObjObj i j,
        HasLiftingProperty sq.ι (p.app k)) :
    HasLiftingProperty ((tensorDiagram K W).map i) p := by
  let adj := _root_.SerrePositivity.PointwiseAdjunction.adjunction K
    (MonoidalClosed.internalHomAdjunction₂ (C := SSet.{u}))
  let (T : SSet.{u}) : ((pointwise K (curriedTensor SSet.{u})).obj T).IsLeftAdjoint :=
    (adj.adj T).isLeftAdjoint
  let push := Functor.PushoutObjObj.ofIsInitialRight
    (pointwise K (curriedTensor SSet.{u})) i (initial.to W) initialIsInitial
  let pull := Functor.PullbackObjObj.ofHasPullback
    (pointwise K (MonoidalClosed.internalHom (C := SSet.{u}))) i p
  apply (adj.hasLiftingProperty_iff push pull).mpr
  apply hW
  apply (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp K).ge
  intro k A B j hj
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  exact (MonoidalClosed.internalHomAdjunction₂.hasLiftingProperty_iff sq
    (evaluatePullbackObjObj K _ i p pull k)).mp (h k j hj sq)

/-- 概要：重み付き錐は各頂点の境界の右類を保つ（Hovey §5）。
方針：単射の pushout product と射影 cofibrant 重みの持ち上げを使う。
規約：元の随伴の右関手の射そのものについて判定する。
使われ方：重み付き錐の自明 fibration とその収縮。 -/
lemma coneSpace_map_boundary_rlp {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k)) :
    SSet.modelCategoryQuillen.I.rlp ((coneSpace K W).map p) := by
  intro X Y i hi
  have : Mono i := SSet.modelCategoryQuillen.I_le_monomorphisms _ hi
  apply ((_root_.SerrePositivity.DiagramModel.WeightedCones.adjunction K W).hasLiftingProperty_iff i p).mp
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensor_map_lifting K W hW i p
  intro k A B j hj sq
  have : Mono j := SSet.modelCategoryQuillen.I_le_monomorphisms _ hj
  have : Mono sq.ι := _root_.SerrePositivity.SimplicialModel.simplicial_pushoutProduct_mono i j sq
  exact SSet.rlp_monomorphisms.ge _ (hp k) sq.ι inferInstance

/-- 概要：重み付き錐は各頂点の Kan fibration を保つ（Hovey §5）。
方針：anodyne と境界の pushout product の持ち上げを移す。
規約：fibration は固定されたホーンの右類でありモデル構造は不要。
使われ方：Kan 値図式の錐空間とそのホモトピー比較。 -/
lemma coneSpace_map_fibration {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ k, Fibration (p.app k)) : Fibration ((coneSpace K W).map p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro X Y i hi
  apply ((_root_.SerrePositivity.DiagramModel.WeightedCones.adjunction K W).hasLiftingProperty_iff i p).mp
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.tensor_map_lifting K W hW i p
  intro k A B j hj sq
  have : Mono j := SSet.modelCategoryQuillen.I_le_monomorphisms _ hj
  have ha : SSet.anodyneExtensions i := by
    rw [SSet.anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp _ _ hi
  exact SSet.anodyneExtensions_pushoutObjObjι' sq ha (p.app k)
    ((SSet.modelCategoryQuillen.fibration_iff _).mp (hp k))

/-- 概要：Kan 値図式の重み付き錐空間は Kan 複体（Hovey §5）。
方針：終対象への射と右随伴による終対象の保存を使う。
規約：頂点ごとの Kan 性と射影 cofibrancy のみを要求する。
使われ方：一般 homotopy 極限を検出する実際の Kan 写像空間。 -/
lemma coneSpace_kanComplex (F : K ⥤ SSet.{u})
    (hF : ∀ k, SSet.KanComplex (F.obj k)) :
    SSet.KanComplex ((coneSpace K W).obj F) := by
  let : (coneSpace K W).IsRightAdjoint :=
    (_root_.SerrePositivity.DiagramModel.WeightedCones.adjunction K W).isRightAdjoint
  apply (isFibrant_iff_of_isTerminal ((coneSpace K W).map (terminal.from F))
    (terminalIsTerminal.isTerminalObj (coneSpace K W) _)).mpr
  apply _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_fibration K W hW
  intro k
  have := hF k
  exact (isFibrant_iff_of_isTerminal ((terminal.from F).app k)
    (terminalIsTerminal.isTerminalObj ((CategoryTheory.evaluation K SSet.{u}).obj k) _)).mp
      inferInstance

/-- 概要：頂点ごとの境界の右類の錐は anodyne 反転後に同型（Hovey §5）。
方針：錐の境界持ち上げ性から切断と単体的収縮を構成する。
規約：任意の anodyne を反転する関手を許し、モデル構造は要求しない。
使われ方：一般 homotopy 極限の係数図式の比較。 -/
lemma coneSpace_map_isIso_of_boundary_rlp {F G : K ⥤ SSet.{u}} (p : F ⟶ G)
    (hp : ∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((coneSpace K W).map p)) :=
  _root_.SerrePositivity.SimplicialModel.MonoRightLiftingContraction.image_isIso _
    (SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpace_map_boundary_rlp K W hW p hp)) L hL

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
