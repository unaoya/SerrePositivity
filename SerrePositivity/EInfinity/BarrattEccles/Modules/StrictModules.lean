module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.AssociativeForget
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGAlgebraMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SemifreePointComparison

/-!
# 厳密 Barratt–Eccles 底上の右加群の準圏

概要：HA §4.2 の加群模型を、同じ台の結合的 dg 代数の右半自由加群で実現する。
方針：既存 dg nerve と安定性を使い、評価・制限の後には出力の解像度を取る。
規約：底の A 上の平坦性や、制限が射影的対象を保つという仮定は加えない。
使われ方：HA §4.5.3 の変わる底への降下の厳密な入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：厳密 BE 底の右加群の導来準圏（HA §4.2.1）。
方針：同じ carrier の dg 代数に半自由加群の dg nerve を適用。
規約：H⁰ に切り下げない。使われ方：一般底上の加群族の fiber。 -/
abbrev strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1} :=
  dgAlgebraDerivedInfinityCategory A ((assocForget A).obj X)

/-- 概要：厳密底上の右加群準圏は安定（HA §4.2.3）。
方針：既存の dg 代数上の安定性を適用。
規約：係数環上の平坦性不要。使われ方：fiber と thick 閉包。 -/
theorem strictModuleInfinity_isStable (X : (operad A).Algebra) :
    SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (strictModuleInfinity A X) :=
  dgAlgebraDerivedInfinityCategory_isStable A ((assocForget A).obj X)

/-- 概要：加群を唯一の対象で評価し、A 上の加群として読む dg 関手（HA §4.2.1）。
方針：半自由加群の全包含・dg 評価・一点定数加群を合成。
規約：評価値の射影性は主張しない。使われ方：解像度付きの台の忘却。 -/
def strictModuleUnderlyingDG (X : (operad A).Algebra) :
    DGFunctor A (SemifreeDGAlgebraModules A ((assocForget A).obj X))
      (RightModule A PUnit.{1}) :=
  ((dgFullSubcategoryInclusion A
    (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
    (dgModuleSemifreeProperty A (dgAlgebraCategory A ((assocForget A).obj X)))).comp
    (moduleEvaluationDG A (dgAlgebraCategory A ((assocForget A).obj X))
      (Opposite.op (DGAlgebraPoint.star)))).comp (ringConstantDG A)

/-- 概要：同じ台を D(A) に送る実 ∞ 関手（HA §4.2.1）。
方針：dg 評価の出力を全関手的に解像し、一点半自由模型を既存 D(A) へ送る。
規約：対象ごとの解像度だけで済ませない。使われ方：単位と fiber の台の比較。 -/
def strictModuleUnderlying (X : (operad A).Algebra) :
    strictModuleInfinity A X ⟶ derivedInfinityCategory A :=
  dgModuleResolvedInfinity A _ PUnit.{1} (strictModuleUnderlyingDG A X) ≫
    (DiagramComparison.semifreePointEquivalence A).hom

/-- 概要：厳密底の正則右加群の指定頂点（HA §4.2.1）。
方針：一対象 dg 圏の表現可能加群に実出力解像度を適用する。
規約：同じ dg 代数の正則加群。使われ方：相対テンソルの単位の比較。 -/
def strictModuleUnit (X : (operad A).Algebra) : (strictModuleInfinity A X) _⦋0⦌ :=
  (dgModuleResolvedInfinity A
    (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
    (dgAlgebraCategory A ((assocForget A).obj X))
    (DGFunctor.id _)).app _
      (Simplex.vertex (representable A (Opposite.op (DGAlgebraPoint.star))))

variable {A}
/-- 概要：全厳密 BE 射に沿う拡大（HA §4.2.3）。
方針：同じ dg 代数射の既存 graph 拡大を使う。
規約：元の入力の A 平坦性不要。使われ方：底の変化の transport。 -/
def strictModuleExtend {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A X ⟶ strictModuleInfinity A Y :=
  dgAlgebraExtensionInfinity A ((assocForget A).map f)

/-- 概要：全厳密 BE 射に沿う制限（HA §4.2.3）。
方針：全包含の後の dg 制限に実出力解像度を適用する。
規約：制限が半自由性や射影性を保つとは仮定しない。
使われ方：native な拡大・制限随伴の右側。 -/
def strictModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X :=
  dgModuleResolvedInfinity A _ (dgAlgebraCategory A ((assocForget A).obj X))
    ((dgFullSubcategoryInclusion A
      (RightModule A (dgAlgebraCategory A ((assocForget A).obj Y)))
      (dgModuleSemifreeProperty A (dgAlgebraCategory A ((assocForget A).obj Y)))).comp
      (dgModuleRestriction A _ _ (dgAlgebraMap A ((assocForget A).map f)).op))

/-- 概要：厳密射の拡大は完全（HA §4.2.3）。
方針：同じ dg 代数射の完全性を再利用。
規約：平坦性の追加なし。使われ方：底変換の thick 閉性。 -/
theorem strictModuleExtend_isExactFunctor {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
      (strictModuleExtend f) :=
  dgAlgebraExtensionInfinity_isExactFunctor A ((assocForget A).map f)

/-- 概要：BE の弱同値に沿う同じ拡大は準圏同値（HA §4.2.3）。
方針：台の複体射を変えない忘却と dg 代数の準同型不変性。
規約：追加の Morita 仮定なし。使われ方：native CAlg への降下。 -/
theorem strictModuleExtend_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleExtend f) :=
  dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso A ((assocForget A).map f) hf

end SerrePositivity.EInfinity.BarrattEccles
