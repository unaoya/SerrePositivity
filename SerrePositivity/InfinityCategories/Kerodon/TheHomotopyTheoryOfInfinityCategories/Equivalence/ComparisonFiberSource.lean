module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanComparisonFibers

/-!
概要：比較射の導来 fiber の path 成分・源成分とその普遍性。
方針：既存の path 置換の引き戻しと頂点 fiber の持ち上げを二つの成分で整理する。
規約：固定する頂点は path の終点。源への射影は標的が Kan なら fibration。
使われ方：Kerodon 4.5.3.24（Tag 02VM）・7.5.4.6（Tag 03BB）、錐の比較射の導来 fiber の実際の射。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
noncomputable section

/-- 概要：導来 fiber から可逆 path への射影。
方針：頂点 fiber の包含と path 置換の第一射影を合成する。
規約：path の終点は固定頂点 b。
使われ方：導来 fiber 間の比較射の path 成分。 -/
def comparisonFiberPath {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p

/-- 概要：導来 fiber から元の比較射の始域への射影。
方針：頂点 fiber の包含と path 置換の源射影を合成する。
規約：始域の点そのものを保持する。
使われ方：始域の比較に関する導来 fiber の引き戻し性。 -/
def comparisonFiberSource {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p

/-- 概要：導来 fiber の path の始点は源成分の比較射による像。
方針：path 置換の引き戻し条件を包含の後で使う。
規約：厳密な射の等式。
使われ方：別の比較射の導来 fiber への持ち上げの整合条件。 -/
lemma comparisonFiberPath_source {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiberPath p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = comparisonFiberSource p b ≫ p := by
  change (_ ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  rfl

/-- 概要：導来 fiber の path の終点は固定頂点に定値。
方針：path 置換の終点射による頂点 fiber の固定条件を使う。
規約：定値射の始域は導来 fiber。
使われ方：導来 fiber の比較射が固定頂点を保つことの検証。 -/
lemma comparisonFiberPath_target {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    comparisonFiberPath p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b := by
  exact (Category.assoc _ _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b)

/-- 概要：整合する path 成分と源成分を導来 fiber へ持ち上げる。
方針：path 置換の引き戻しへ持ち上げてから終点の頂点 fiber へ持ち上げる。
規約：Kan 性や fibration 性は不要。
使われ方：同じ底上の比較の導来 fiber の射と引き戻しの普遍性。 -/
def comparisonFiberLift {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b (pullback.lift a s h₀) (by
    change pullback.lift a s h₀ ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b
    rw [← Category.assoc, pullback.lift_fst]
    exact h₁)

/-- 概要：導来 fiber への持ち上げの path 成分は指定した射。
方針：二つの持ち上げの第一成分を計算する。
規約：整合条件の証明の選択に依存しない。
使われ方：導来 fiber の比較射の path 成分の自然性。 -/
lemma comparisonFiberLift_path {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b) :
    comparisonFiberLift p b a s h₀ h₁ ≫ comparisonFiberPath p b = a := by
  simp only [comparisonFiberLift, comparisonFiberPath, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, pullback.lift_fst]

/-- 概要：導来 fiber への持ち上げの源成分は指定した射。
方針：二つの持ち上げの第二成分を計算する。
規約：整合条件の証明の選択に依存しない。
使われ方：導来 fiber の比較射の源成分の自然性。 -/
lemma comparisonFiberLift_source {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B) (s : T ⟶ E)
    (h₀ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = s ≫ p)
    (h₁ : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b) :
    comparisonFiberLift p b a s h₀ h₁ ≫ comparisonFiberSource p b = s := by
  simp only [comparisonFiberLift, comparisonFiberSource, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection, pullback.lift_snd]

/-- 概要：導来 fiber への射は path 成分と源成分で決まる。
方針：頂点 fiber の包含後に引き戻しの二成分で比較する。
規約：始域は任意の単体集合。
使われ方：導来 fiber の引き戻し性と比較射の可換式。 -/
lemma comparisonFiber_hom_ext {T E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {f g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b}
    (hp : f ≫ comparisonFiberPath p b = g ≫ comparisonFiberPath p b)
    (hs : f ≫ comparisonFiberSource p b = g ≫ comparisonFiberSource p b) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (hs.trans (Category.assoc _ _ _).symm)

/-- 概要：標的が Kan なら導来 fiber の元の始域への射影は Kan fibration。
方針：源成分を固定し、両端点を同時指定して path のホーンを充填する。
規約：元の比較射やその始域の Kan 性は要求しない。
使われ方：始域の同値で誘導する導来 fiber の比較の同値性。 -/
instance comparisonFiberSource_fibration {E B : SSet.{u}} [KanComplex B]
    (p : E ⟶ B) (b : B _⦋0⦌) : Fibration (comparisonFiberSource p b) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro T U j hj
  have : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints B) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance j hj
  constructor
  intro a s sq
  let e := asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B)
  have he (i : Fin 2) : e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) := by
    change e.inv ≫ e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = _
    rw [Iso.inv_hom_id_assoc]
  let sqP : CommSq (a ≫ comparisonFiberPath p b ≫ e.hom) j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints B) (prod.lift (SSet.const b) (s ≫ p)) := ⟨by
    apply prod.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_fst, prod.lift_fst]
      change a ≫ comparisonFiberPath p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = j ≫ SSet.const b
      rw [comparisonFiberPath_target, SSet.comp_const, SSet.comp_const]
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_snd, prod.lift_snd]
      change a ≫ comparisonFiberPath p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = j ≫ s ≫ p
      rw [comparisonFiberPath_source]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ p) sq.w)).trans (Category.assoc _ _ _)⟩
  let v := sqP.lift ≫ e.inv
  have hv₀ : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = s ≫ p := by
    rw [Category.assoc, he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_snd, ← Category.assoc,
      sqP.fac_right, prod.lift_snd]
  have hv₁ : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = SSet.const b := by
    rw [Category.assoc, he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_fst, ← Category.assoc,
      sqP.fac_right, prod.lift_fst]
  let l := comparisonFiberLift p b v s hv₀ hv₁
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := comparisonFiberLift_source _ _ _ _ _ _ }⟩⟩
  apply comparisonFiber_hom_ext p b
  · rw [Category.assoc, comparisonFiberLift_path]
    change j ≫ sqP.lift ≫ e.inv = a ≫ comparisonFiberPath p b
    rw [← Category.assoc, sqP.fac_left]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, comparisonFiberLift_source]
    exact sq.w.symm

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
