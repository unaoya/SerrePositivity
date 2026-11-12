module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram

/-!
概要：底の辺の空間全体に依存する fiber transport。
方針：係数とパラメーターの直積上で一つの prism を持ち上げ、終点を curry する。
規約：各辺で独立な選択を行わず、全高次パラメーターを保つ。
使われ方：Kerodon Definition 5.2.8.1（Tag 02RM）、Lemma 5.6.9.1（Tag 02SN） の普遍輸送の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：始点 fiber への係数射を指定したパラメーター付き輸送の証人。
方針：全パラメーターに依存する prism と、その終点の fiber 値の射を保持する。
規約：係数 K とパラメーター L は任意の単体集合。
使われ方：写像空間上の普遍輸送を単体集合の射として構成する。 -/
structure FiberTransportFamily {E B K L : SSet.{u}} (p : E ⟶ B)
    {a b : B _⦋0⦌} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B) where
  endpoint : K ⊗ L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b
  prism : (Δ[1] : SSet.{u}) ⊗ (K ⊗ L) ⟶ E
  start : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ L) ≫ prism = fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
  finish : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L) ≫ prism = endpoint ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  over_base : prism ≫ p = (Δ[1] ◁ snd K L) ≫ γ

/-- 概要：パラメーター付き輸送を fiber 間の関手空間への射にする。
方針：終点の係数変数を curry する。
規約：パラメーターの高次単体に作用する実際の射。
使われ方：普遍 pointed-space 輸送の写像空間比較。 -/
def FiberTransportFamily.map {E B K L : SSet.{u}} {p : E ⟶ B} {a b : B _⦋0⦌}
    {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
    (T : FiberTransportFamily (b := b) p f γ) : L ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  curry T.endpoint

/-- 概要：底の族の指定端点は係数を忘れる引き戻し後も定値。
方針：prism の端点の自然性を使う。
規約：係数 K は任意。
使われ方：全パラメーター上の持ち上げの初期条件と終点 fiber の条件。 -/
lemma fiberTransportFamily_base_endpoint {B K L : SSet.{u}} (i : Fin 2)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B) (b : B _⦋0⦌)
    (hγ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i L ≫ γ = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (K ⊗ L) ≫ (Δ[1] ◁ snd K L) ≫ γ = SSet.const b := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hγ, SSet.comp_const]

/-- 概要：left fibration では指定した底の全ての辺の族に対する輸送族が存在する。
方針：係数とパラメーターの直積上で始点を固定して持ち上げ、終点を fiber に入れる。
規約：底・係数・パラメーターの quasicategory 性を要求しない。
使われ方：Kerodon Definition 5.2.8.1（Tag 02RM） の left fibration の場合。 -/
noncomputable def fiberTransportFamily {E B K L : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {a b : B _⦋0⦌} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 L ≫ γ = SSet.const a)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ γ = SSet.const b) : FiberTransportFamily (b := b) p f γ := by
  let v := fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
  let β := (Δ[1] ◁ snd K L) ≫ γ
  have hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (K ⊗ L) ≫ β := by
    dsimp only [v, β]
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
    exact (fiberTransportFamily_base_endpoint 0 γ a h₀).symm
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_lift_prism p v β hv
  let H := h.choose
  have hH₀ := h.choose_spec.1
  have hHp := h.choose_spec.2
  have hH₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L) ≫ H) ≫ p = SSet.const b := by
    rw [Category.assoc, hHp]
    exact fiberTransportFamily_base_endpoint 1 γ b h₁
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L) ≫ H) hH₁,
    H, hH₀, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _).symm, hHp⟩

/-- 概要：同じ底の族と始点を持つ二つの輸送族の終点は族全体で関手同型。
方針：全パラメーター上の可縮な延長空間の終点を比較する。
規約：各頂点での同型の存在だけに弱めない。
使われ方：選択した普遍輸送の写像空間比較を標準比較と同定する。 -/
noncomputable def FiberTransportFamily.endpointIso {E B K L : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T.endpoint U.endpoint := by
  let β := (Δ[1] ◁ snd K L) ≫ γ
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ (K ⊗ L)
  let v := snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫ fst K L ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a
  have hTi : i ≫ T.prism = v := by
    dsimp only [i, v]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫ z) T.start
  have hUi : i ≫ U.prism = v := by
    dsimp only [i, v]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) (K ⊗ L) ≫ z) U.start
  have hv : v ≫ p = i ≫ β := by rw [← hTi, Category.assoc, T.over_base]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeExtensionFiberEndpoint_witnessIso p β i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne 1 (K ⊗ L)) v hv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L)) b
    (fiberTransportFamily_base_endpoint 1 γ b h₁) T.prism U.prism T.over_base U.over_base
    hTi hUi T.endpoint U.endpoint T.finish U.finish

/-- 概要：同じ輸送の二つの選択は写像空間上の射として関手同型。
方針：終点族の関手同型を curry する。
規約：標的 fiber の Kan 性だけを left fibration 性から導く。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN）、普遍輸送の比較の選択独立性。 -/
noncomputable def FiberTransportFamily.mapIso {E B K L : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a)
    (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ γ = SSet.const b)
    (T U : FiberTransportFamily (b := b) p f γ) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso T.map U.map := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  exact (T.endpointIso p f γ h₁ U).curry

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
