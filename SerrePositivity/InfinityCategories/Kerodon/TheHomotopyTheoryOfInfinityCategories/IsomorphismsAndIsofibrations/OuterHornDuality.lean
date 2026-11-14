module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.OuterHornConverse
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：外側ホーンの充填条件の左右の双対。
方針：ホーン・標準単体・辺を反転し、反転した充填から元の充填を復元する。
規約：最初・最後の指定した辺を正確に保つ。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F）、HTT Proposition 1.2.4.3。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：最初のホーンの反転の添字を最後のホーンへ正規化する。
方針：零の Fin.rev の式を部分複体の同型にする。
規約：各次数の単体そのものは変えない。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の左右の交換。 -/
def initialHornReverseIndexIso (n : ℕ) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ≅ horn (n + 2) (0 : Fin (n + 3)).rev :=
  Subcomplex.eqToIso (by rw [Fin.rev_zero])

/-- 概要：最後のホーンの反転の添字を最初のホーンへ正規化する。
方針：最後の元の Fin.rev の式を部分複体の同型にする。
規約：各次数の単体そのものは変えない。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の左右の交換。 -/
def finalHornReverseIndexIso (n : ℕ) :
    (horn (n + 2) 0 : SSet.{u}) ≅ horn (n + 2) (Fin.last (n + 2)).rev :=
  Subcomplex.eqToIso (by rw [Fin.rev_last])

/-- 概要：最初のホーンからの射を最後のホーンからの射へ反転する。
方針：反転写像に添字の正規化を前合成する。
規約：反転した標的への射になる。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇒(2)。 -/
def reverseInitialHornMap {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X.op :=
  (initialHornReverseIndexIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 2) 0 σ

/-- 概要：最後のホーンからの射を最初のホーンからの射へ反転する。
方針：反転写像に添字の正規化を前合成する。
規約：反転した標的への射になる。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の逆向きの双対化。 -/
def reverseFinalHornMap {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X) :
    (horn (n + 2) 0 : SSet.{u}) ⟶ X.op :=
  (finalHornReverseIndexIso n).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 2) (Fin.last (n + 2)) σ

/-- 概要：最初のホーンの反転は最初の辺を最後の辺へ移す。
方針：ホーンの反転写像を有限順序集合の二つの端点で計算する。
規約：単体の値も opObjEquiv で反転した値と一致する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の固定する辺の照合。 -/
lemma reverseInitialHornMap_edge {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) 0 : SSet.{u}) ⟶ X) :
    (reverseInitialHornMap n σ).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} n) =
      SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n)) := by
  change SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) _) = _
  congr 1
  apply congrArg
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i
  · change (Fin.last (n + 2)).rev = (0 : Fin (n + 3))
    exact Fin.rev_last (n + 2)
  · change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} n).val ((1 : Fin 2).rev)).rev = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n).val 1
    rw [show (1 : Fin 2).rev = 0 from by decide]
    change (⟨n + 1, by omega⟩ : Fin (n + 3)).rev = (1 : Fin (n + 3))
    apply Fin.ext
    rw [Fin.val_rev]
    have h : (1 : Fin (n + 3)).val = 1 := by simp
    rw [h]
    change n + 3 - ((n + 1) + 1) = 1
    omega

/-- 概要：最後のホーンの反転は最後の辺を最初の辺へ移す。
方針：ホーンの反転写像を二つの端点で計算する。
規約：元の辺の一単体を正確に反転する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の逆向きの固定条件。 -/
lemma reverseFinalHornMap_edge {X : SSet.{u}} (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X) :
    (reverseFinalHornMap n σ).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) =
      SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} n)) := by
  change SSet.opObjEquiv.symm (σ.app (Opposite.op ⦋1⦌) _) = _
  congr 1
  apply congrArg
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i
  · apply Fin.ext
    change (n + 2) - (1 : Fin (n + 3)).val = n + 1
    have h : (1 : Fin (n + 3)).val = 1 := by simp
    rw [h]
    omega
  · change (0 : Fin (n + 3)).rev = Fin.last (n + 2)
    exact Fin.rev_zero (n + 2)

/-- 概要：最初のホーンの反転添字の正規化は包含を保つ。
方針：部分複体の等式による同型を計算する。
規約：周囲は同じ標準単体。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填の復元。 -/
lemma initialHornReverseIndexIso_hom_ι (n : ℕ) :
    (initialHornReverseIndexIso.{u} n).hom ≫ (horn (n + 2) (0 : Fin (n + 3)).rev).ι =
      (horn (n + 2) (Fin.last (n + 2))).ι := rfl

/-- 概要：最後のホーンの反転添字の正規化は包含を保つ。
方針：部分複体の等式による同型を計算する。
規約：周囲は同じ標準単体。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の充填の復元。 -/
lemma finalHornReverseIndexIso_hom_ι (n : ℕ) :
    (finalHornReverseIndexIso.{u} n).hom ≫ (horn (n + 2) (Fin.last (n + 2)).rev).ι =
      (horn (n + 2) 0).ι := rfl

/-- 概要：反転した辺の最後のホーンの充填から元の辺の最初のホーンを充填する。
方針：指定した辺を反転し、得られた充填を反転して戻す。
規約：quasicategory 性はこの移送には不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇒(2) の双対化。 -/
lemma hasInitialHornFillers_of_hasFinalHornFillers_op {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e := by
  intro n σ hσ
  let τ := reverseInitialHornMap n σ
  have hτ : τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e).edge := by
    rw [reverseInitialHornMap_edge, hσ]
    rfl
  obtain ⟨F, hF⟩ := he n τ hτ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 2) 0 σ F
  apply (cancel_epi (initialHornReverseIndexIso n).hom).1
  rw [← Category.assoc, initialHornReverseIndexIso_hom_ι]
  exact hF

/-- 概要：反転した辺の最初のホーンの充填から元の辺の最後のホーンを充填する。
方針：指定した辺を反転し、得られた充填を反転して戻す。
規約：quasicategory 性はこの移送には不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の逆向きの双対化。 -/
lemma hasFinalHornFillers_of_hasInitialHornFillers_op {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers e := by
  intro n σ hσ
  let τ := reverseFinalHornMap n σ
  have hτ : τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e).edge := by
    rw [reverseFinalHornMap_edge, hσ]
    rfl
  obtain ⟨F, hF⟩ := he n τ hτ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 2) (Fin.last (n + 2)) σ F
  apply (cancel_epi (finalHornReverseIndexIso n).hom).1
  rw [← Category.assoc, finalHornReverseIndexIso_hom_ι]
  exact hF

/-- 概要：最初のホーンの充填条件は一単体の等式に沿って移せる。
方針：固定する辺の等式を合成する。
規約：端点の表示が異なってもよい。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の二重反転の処理。 -/
lemma hasInitialHornFillers_congr {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y'} (h : e.edge = f.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers f := by
  constructor
  · intro he n σ hσ
    exact he n σ (hσ.trans h.symm)
  · intro hf n σ hσ
    exact hf n σ (hσ.trans h)

/-- 概要：標的の同型は最初のホーンの充填条件を保つ。
方針：ホーンを逆同型で戻して充填し、順方向の同型で写す。
規約：指定した辺も同じ同型で写す。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の二重反転からの帰還。 -/
lemma HasInitialHornFillers.map_iso {X Y : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e) (q : X ≅ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers (e.map ((truncation 2).map q.hom)) := by
  intro n σ hσ
  have hc : (σ ≫ q.inv).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) = e.edge := by
    change q.inv.app (Opposite.op ⦋1⦌) (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n)) = _
    change σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge.{u} n) =
      q.hom.app (Opposite.op ⦋1⦌) e.edge at hσ
    rw [hσ]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app q.hom_inv_id (Opposite.op ⦋1⦌)) e.edge
  obtain ⟨F, hF⟩ := he n (σ ≫ q.inv) hc
  refine ⟨F ≫ q.hom, ?_⟩
  rw [← Category.assoc, hF, Category.assoc, q.inv_hom_id, Category.comp_id]

/-- 概要：可逆な辺を最初の辺に持つ外側ホーンは全て充填できる。
方針：辺を反転し、最後のホーンの定理を適用して戻す。
規約：仮定は quasicategory 性と指定した辺の可逆性。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇒(2)、HTT Proposition 1.2.4.3。 -/
lemma hasInitialHornFillers_of_isInvertibleEdge {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e :=
  hasInitialHornFillers_of_hasFinalHornFillers_op e
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.IsInvertibleEdge.op he))

/-- 概要：最初の外側ホーンの充填条件を持つ辺は可逆。
方針：二重反転の同型で条件を移し、反転した辺に最後のホーンの逆向きを適用する。
規約：仮定は元の quasicategory 性のみ。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (2)⇒(1)、HTT Proposition 1.2.4.3。 -/
lemma isInvertibleEdge_of_hasInitialHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have hmap := HasInitialHornFillers.map_iso he (SSet.opFunctorCompOpFunctorIso.app X).symm
  have hdouble : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers (X := X.op.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := X) e)) :=
    (hasInitialHornFillers_congr (X := X.op.op)
      (e := e.map ((truncation 2).map (SSet.opFunctorCompOpFunctorIso.app X).inv))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)) rfl).1 hmap
  have hfinal : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) :=
    hasFinalHornFillers_of_hasInitialHornFillers_op (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) hdouble
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_op_iff e).1
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.isInvertibleEdge_of_hasFinalHornFillers (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e) hfinal)

/-- 概要：辺の可逆性は最初の外側ホーンの充填条件と同値。
方針：反転による順方向と逆方向を組み合わせる。
規約：全ての次数二以上を量化し、余分な全射の仮定はない。
使われ方：HTT Proposition 1.2.4.3、Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇔(2)。 -/
@[kerodon 019F]
lemma isInvertibleEdge_iff_hasInitialHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasInitialHornFillers e :=
  ⟨hasInitialHornFillers_of_isInvertibleEdge e, isInvertibleEdge_of_hasInitialHornFillers e⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.4.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_hasInitialHornFillers
