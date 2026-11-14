module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の射の頂点上の fiber の直接構成。
方針：各次数で頂点の定値単体へ写る元の部分型を取り、射の自然性で引き戻す。
規約：point 上の fiber をモデル構造なしで扱う。
使われ方：HTT Proposition 1.2.12.4、Kerodon Proposition 4.4.2.14（Tag 01NU）。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：射 p の頂点 b 上の fiber。
方針：p の値が b の定値単体と一致する単体の部分型を取る。
規約：全次数で同じ頂点 b を固定する。
使われ方：Kerodon Construction 4.6.5.1（Tag 01KX）、slice 射影の fiber。 -/
def vertexFiber {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) : SSet.{u} where
  obj n := {s : E.obj n // p.app n s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n.unop.len}
  map {n m} α := ↾fun s ↦ ⟨E.map α s.val, by
    calc
      _ = B.map α (p.app n s.val) := ConcreteCategory.congr_hom (p.naturality α) s.val
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b m.unop.len := by
        rw [s.property]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback b α.unop⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact CategoryTheory.Functor.map_id_apply E _ s.val
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact CategoryTheory.Functor.map_comp_apply E α β s.val

/-- 概要：fiber の単体を元の単体集合へ含める。
方針：部分型の値を取る。
規約：各次数で単射。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の fiber の持ち上げ問題。 -/
def vertexFiberι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) : vertexFiber p b ⟶ E where
  app _ := ↾Subtype.val
  naturality {n m} α := rfl

/-- 概要：fiber の包含の後で p を適用すると頂点 b に定値。
方針：各単体に添えた条件を読む。
規約：定値射の始域は fiber 自身。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の可換四角形。 -/
lemma vertexFiberι_comp {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    vertexFiberι p b ≫ p = SSet.const b := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact s.property

/-- 概要：値が b に定値となる射は fiber へ持ち上がる。
方針：各単体の値に固定条件を添える。
規約：固定条件 hf は射の等式。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の fiber の普遍性。 -/
def vertexFiberLift {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ E) (hf : f ≫ p = SSet.const b) : A ⟶ vertexFiber p b where
  app n := ↾fun a ↦ ⟨f.app n a, ConcreteCategory.congr_hom (NatTrans.congr_app hf n) a⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (f.naturality α) a

/-- 概要：fiber への持ち上げを元へ含めると元の射。
方針：部分型の値を計算する。
規約：hf の証明の選択には依存しない。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の持ち上げの確認。 -/
lemma vertexFiberLift_ι {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (f : A ⟶ E) (hf : f ≫ p = SSet.const b) : vertexFiberLift p b f hf ≫ vertexFiberι p b = f := rfl

/-- 概要：fiber への二つの射は元の単体集合への合成が同じなら等しい。
方針：部分型の値の等式を使う。
規約：任意の始域からの射を扱う。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の普遍性の一意性。 -/
lemma vertexFiber_hom_ext {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {f g : A ⟶ vertexFiber p b} (h : f ≫ vertexFiberι p b = g ≫ vertexFiberι p b) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h n) a

/-- 概要：trivial Kan fibration の頂点上の fiber は可縮な Kan 複体。
方針：fiber の境界を元へ含め、下を定値射として p の持ち上げ性を使う。
規約：元の標的に quasicategory 性を仮定しない。
使われ方：HTT Proposition 1.2.12.4、Kerodon Proposition 4.4.2.14（Tag 01NU） の順方向。 -/
lemma vertexFiber_isContractibleKan {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (b : B _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (vertexFiber p b) := by
  intro n a
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (boundary n).ι inferInstance
  have sq : CommSq (a ≫ vertexFiberι p b) (boundary n).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  exact sq.fac_left

/-- 概要：右ファイブレーションの頂点上の fiber は Kan 複体。
方針：下を定値射とした右ホーンの持ち上げと A3b の Kan 判定を使う。
規約：標的の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、写像空間の fiber 模型。 -/
@[kerodon 019E]
lemma vertexFiber_kanComplex {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (b : B _⦋0⦌) : KanComplex (vertexFiber p b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i hi a
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i hi)
  have sq : CommSq (a ≫ vertexFiberι p b) (horn (n + 1) i).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply vertexFiber_hom_ext p b
  rw [Category.assoc, vertexFiberLift_ι]
  exact sq.fac_left

/-- 概要：右ファイブレーションの一つの fiber に属する辺は可逆。
方針：fiber の Kan 性から辺の可逆性を得て、包含で元の単体集合へ写す。
規約：base の quasicategory 性は不要。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の特別な外側ホーン。 -/
lemma rightFibration_isInvertibleEdge_of_constant_image {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌) (s : E _⦋1⦌)
    (hs : p.app (Opposite.op ⦋1⦌) s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s) := by
  have := vertexFiber_kanComplex p b
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (X := vertexFiber p b) ⟨s, hs⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e :=
    IsGroupoid.all_isIso (C := hoFunctor.obj (vertexFiber p b))
      (SSet.Truncated.HomotopyCategory.homMk e)
  have hm := he.map (vertexFiberι p b)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl).mp hm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.4.2" (partial := component) "仮定：reduced pairing の片側の単位 fiber の射影が trivial Kan fibration（HA の仮定 (b) と一致）。結論：その射影のもう一方の単位点での fiber が可縮 Kan となる（原典冒頭の二つの単位を固定した fiber の可縮性に一致する部分）。全空間 M におけるその点の始対象性と weakly reduced 性は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan
attribute [cite HTT "2.4.2.4" (partial := component) "仮定：任意の単体集合の射 p（原典より弱い）。結論：rightFibration_iff_cartesianFibration_all_edges は (1)⇔(2) を正確に与え、vertexFiber_kanComplex と合わせて (2)⇒(3) も得る。(3)⇒(1)/(2) は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex
