module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cartesian・cocartesian fibration と inner fibration の接続。
方針：内ホーンの rlp と指定端点を持つ cartesian 辺の存在を組み合わせる。
規約：fibration 性は Prop とし、持ち上げの選択を構造に含めない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、F1a の fibration の基礎。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cartesian fibration の射の性質。
方針：内ホーンの rlp と、終点を指定した cartesian lift の存在を要求する。
規約：底の quasicategory 性は定義に含めない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA） の cartesian 側。 -/
@[kerodon 01UA]
def cartesianFibrations : MorphismProperty SSet.{u} := fun X B p ↦
  innerFibrations p ∧ ∀ (x : X _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ B),
    stdSimplex.δ 0 ≫ e = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) →
    ∃ f : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ 0 ≫ f = SSet.yonedaEquiv.symm x ∧ f ≫ p = e ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv f)

/-- 概要：cocartesian fibration の射の性質。
方針：内ホーンの rlp と、始点を指定した cocartesian lift の存在を要求する。
規約：辺とその端点の一致は射の厳密な等式で課す。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA） の cocartesian 側。 -/
def cocartesianFibrations : MorphismProperty SSet.{u} := fun X B p ↦
  innerFibrations p ∧ ∀ (x : X _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ B),
    stdSimplex.δ 1 ≫ e = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) →
    ∃ f : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ 1 ≫ f = SSet.yonedaEquiv.symm x ∧ f ≫ p = e ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv f)

/-- 概要：cartesian fibration 性の型クラス。
方針：射の性質への所属を保持する。
規約：選択された lift を持たない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、cartesian transport の入力。 -/
@[kerodon 01UA]
class CartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop where
  mem : cartesianFibrations p

/-- 概要：cocartesian fibration 性の型クラス。
方針：射の性質への所属を保持する。
規約：選択された lift を持たない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、covariant transport の入力。 -/
@[kerodon 01UA]
class CocartesianFibration {X B : SSet.{u}} (p : X ⟶ B) : Prop where
  mem : cocartesianFibrations p

/-- 概要：cartesian fibration は inner fibration。
方針：定義の第一条件を取り出す。
規約：全空間や底の仮定は不要。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、fiber の quasicategory 性。 -/
instance cartesianFibration_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CartesianFibration p] : InnerFibration p := ⟨CartesianFibration.mem.1⟩

/-- 概要：cocartesian fibration は inner fibration。
方針：定義の第一条件を取り出す。
規約：全空間や底の仮定は不要。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、fiber の quasicategory 性。 -/
instance cocartesianFibration_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] : InnerFibration p := ⟨CocartesianFibration.mem.1⟩

/-- 概要：right fibration は cartesian fibration。
方針：一次の最後のホーンから辺を持ち上げ、全辺の cartesian 性を使う。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、A2d の右ファイブレーションとの整合。 -/
instance rightFibration_cartesianFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] : CartesianFibration p where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (1 : Fin 2) (by decide))
    have sq : CommSq (SSet.const x) (horn 1 1).ι p e := by
      constructor
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc]
        change SSet.const (p.app (Opposite.op ⦋0⦌) x) = stdSimplex.δ 0 ≫ e
        rw [he, SSet.yonedaEquiv_symm_zero]
      · exact (hj rfl).elim
    refine ⟨sq.lift, ?_, sq.fac_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_rightFibration p _⟩
    rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, SSet.comp_const,
      SSet.yonedaEquiv_symm_zero]

/-- 概要：left fibration は cocartesian fibration。
方針：一次の零番目ホーンから辺を持ち上げ、全辺の cocartesian 性を使う。
規約：底の quasicategory 性を仮定しない。
使われ方：Kerodon Definition 5.1.4.1（Tag 01UA）、A2d の左ファイブレーションとの整合。 -/
instance leftFibration_cocartesianFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : CocartesianFibration p where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin 2) (by decide))
    have sq : CommSq (SSet.const x) (horn 1 0).ι p e := by
      constructor
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc]
        change SSet.const (p.app (Opposite.op ⦋0⦌) x) = stdSimplex.δ 1 ≫ e
        rw [he, SSet.yonedaEquiv_symm_zero]
    refine ⟨sq.lift, ?_, sq.fac_right, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration p _⟩
    rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left, SSet.comp_const,
      SSet.yonedaEquiv_symm_zero]

/-- 概要：cartesian fibration は合成で閉じる。
方針：二段階の辺の持ち上げと cartesian 辺の合成則を使う。
規約：合成は p ≫ q の順。
使われ方：Kerodon §5.1.4（Tag 01U9）、fibration の合成の閉性。 -/
instance cartesianFibration_comp {X Y B : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ B)
    [CartesianFibration p] [CartesianFibration q] : CartesianFibration (p ≫ q) where
  mem := by
    refine ⟨innerFibrations.comp_mem p q (InnerFibration.mem (q := p))
      (InnerFibration.mem (q := q)), ?_⟩
    intro x e he
    obtain ⟨g, hg, hgq, hgc⟩ := CartesianFibration.mem (p := q) |>.2
      (p.app (Opposite.op ⦋0⦌) x) e he
    obtain ⟨f, hf, hfp, hfc⟩ := CartesianFibration.mem (p := p) |>.2 x g hg
    refine ⟨f, hf, ?_, hfc.comp ?_⟩
    · rw [← Category.assoc, hfp, hgq]
    · have h : p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) = SSet.yonedaEquiv g := by
        rw [← SSet.yonedaEquiv_comp, hfp]
      rwa [h]

/-- 概要：cocartesian fibration は合成で閉じる。
方針：二段階の辺の持ち上げと cocartesian 辺の合成則を使う。
規約：合成は p ≫ q の順。
使われ方：Kerodon §5.1.4（Tag 01U9）、fibration の合成の閉性。 -/
instance cocartesianFibration_comp {X Y B : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ B)
    [CocartesianFibration p] [CocartesianFibration q] : CocartesianFibration (p ≫ q) where
  mem := by
    refine ⟨innerFibrations.comp_mem p q (InnerFibration.mem (q := p))
      (InnerFibration.mem (q := q)), ?_⟩
    intro x e he
    obtain ⟨g, hg, hgq, hgc⟩ := CocartesianFibration.mem (p := q) |>.2
      (p.app (Opposite.op ⦋0⦌) x) e he
    obtain ⟨f, hf, hfp, hfc⟩ := CocartesianFibration.mem (p := p) |>.2 x g hg
    refine ⟨f, hf, ?_, hfc.comp ?_⟩
    · rw [← Category.assoc, hfp, hgq]
    · have h : p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv f) = SSet.yonedaEquiv g := by
        rw [← SSet.yonedaEquiv_comp, hfp]
      rwa [h]

/-- 概要：inner fibration の各 fiber は quasicategory。
方針：定値な底の上で内ホーンを持ち上げ、fiber の普遍性を使う。
規約：底が quasicategory であることを仮定しない。
使われ方：Kerodon §5.1.4（Tag 01U9）、cartesian・cocartesian fibration の fiber。 -/
lemma vertexFiber_quasicategory_of_innerFibration {X B : SSet.{u}} (p : X ⟶ B)
    [InnerFibration p] (b : B _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
  constructor
  intro n i a h0 hn
  have := InnerFibration.mem (q := p) _ (innerHornInclusions.intro i h0 hn)
  have sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (horn (n + 2) i).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact sq.fac_left.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.2.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
attribute [cite HTT "2.4.2.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
attribute [cite HTT "2.4.2.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cartesianFibration_comp
attribute [cite HTT "3.1.2.1" (partial := special) "仮定：Cartesian p と任意の K（Lean が強い：p を right fibration に限定）。結論：同じ ihom K による pK が right、従って Cartesian fibration となり一致。この場合は p と pK の全辺が Cartesian なので点ごとの iff も両辺が成立する。一般の Cartesian fibration の指数は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_cartesianFibration
attribute [cite HTT "3.2.2.12" (partial := special) "仮定：p:X→S は Cartesian、q:Y→Z は cocartesian（Lean が強い：S=Δ⁰、q を left fibration に限定）。結論：この場合は Y′=Fun(X,Y),Z′=Fun(X,Z) と取れ、q′ が left、従って cocartesian fibration となる。全 Y と Y′ の辺が cocartesian なので (2) の辺の条件も両側が成立し一致。一般の相対 q には拡張しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_cocartesianFibration
attribute [cite HTT "4.1.2.15" (partial := special) "仮定：余デカルトファイブレーション p（Lean が強い：p が左ファイブレーションで、余デカルトファイブレーションの instance がある）。結論：同じ切片で右アノダイン射の引き戻しが右アノダインとなる（滑らかさの条件 (1) と一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibration_cocartesianFibration
attribute [cite HTT "4.1.3.2" (partial := special) "仮定：デカルトファイブレーション p の全頂点繊維が弱可縮（Lean が強い：p が右ファイブレーションで、デカルトファイブレーションの instance がある）。結論：同じ p に対する自明 Kan ファイブレーションの判定を直ちに共終性の宣言に適用すると p は共終（一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibration_cartesianFibration
attribute [cite HTT "5.5.3.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
attribute [cite HTT "5.5.3.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
