-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.AnimatedDomain（仮。原典 Def 8.2 の定義域「導来 p 完備な animated R 代数」）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.1・§5（配置、W9-II-24）、単位 A7-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.HomologicalAlgebra.DerivedInfinity.VertexPredicates

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyCategoryComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
-- 本ファイルは drafts/A2/AnimatedAlgebra.lean、drafts/DerivedGeneral/CompletionFunctor.lean だけを import する（A5 より先に置く）。

/-!
# animated 代数の定義域（G-A7-1、BS 著者版 Def 8.2 の定義域）

## 概要
`AnimatedAlgebra R`（A2-1 の P_Σ(Poly_R)）の底の D(R) 対象 `animatedForget`、導来 p 完備な animated R 代数の充満部分 ∞ 圏 `CompleteAnimatedAlgebra R`、
導来 p 完備化 `animatedCompletion`、離散な導来 p 完備環の埋め込みとの整合。

## 方針
W9-II-24 で A7/AnimatedPerfectoidization.lean から切り出した。D45 改訂後の A5（Prop 8.5 の animated 版、`perfectionComparison_isIso_animated`）が
この定義域を使うので、A5 より先に import できる独立ファイルにする。所有単位は A7-1 のまま。

## 規約
基底は Not 8.1 の完全 prism（R = A/d）。導来 p 完備性は底の D(R) 対象で判定する。

## 使われ方
A5-1（Prop 8.5 の animated 版）、A7-1（Def 8.2 の animated 版、Prop 8.13）、A7-2（X = S_perfd ⊗̂^L_S S_perfd）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## G-A7-1：底の加群、完備性、完備化 -/

/-- A2 の多項式生成系を通常の R 代数に送る。 -/
def polynomialAlgebras : Poly R ⥤ PerfectoidizationInterface.A_R R where
  obj Q := PerfectoidizationInterface.ofAlgebra R (MvPolynomial (Fin Q.n) R)
  map f := Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext r; exact f.commutes r)
  map_id := by sorry -- 多項式代数の恒等準同型
  map_comp := by sorry -- R 代数準同型の合成

def polynomialDiscreteDiagram :
    (SSet.uliftFunctor.{u+1,u}).obj (polyNerve R) ⟶ nerve (PerfectoidizationInterface.A_R R) where
  app n := ↾fun x => ((polynomialAlgebras R).mapComposableArrows _).obj x.down
  naturality := by sorry -- 小さい nerve の各単体を多項式代数の関手で送る

/-- 概要：animated R 代数の底の D(R) 対象：Poly_R → D(R)（多項式環を離散加群として）の sifted 余極限を保つ延長。
方針：A2-1 の `exists_siftedExtension`（HTT 5.5.8.15）。
規約：`AnimatedAlgebra R ⟶ derivedInfinityCategory R`。
使われ方：導来 p 完備性の定義、A2-2 の Δ との整合（Δ の底）。 -/
def animatedForget : AnimatedAlgebra R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R :=
  Classical.choose (show ∃ U : AnimatedAlgebra R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits U ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (polyYoneda R ≫ U) (polynomialDiscreteDiagram R ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding R)) from by
    sorry) -- 要確認：BS-D4 で exists_siftedExtension の sifted 保存と制限同型に接続

/-! 連結性・p完備性の述語と旧名の略記は、本体の
`HomologicalAlgebra/DerivedInfinity/VertexPredicates` を使う。 -/

def isAnimatedComplete (x : (AnimatedAlgebra R) _⦋0⦌) : Prop :=
  isPCompleteVertex p R ((animatedForget R).app _ x)

/-- 概要：導来 p 完備な animated R 代数の充満部分 ∞ 圏（原典 Def 8.2 の定義域）。
方針：`animatedForget` の像を通常の導来圏へ移し、主元 p の `IsComplete` による fullSubcomplex を取る。
規約：`SSet` の部分複体。
使われ方：Def 8.2、Prop 8.13。 -/
def CompleteAnimatedAlgebra : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (AnimatedAlgebra R) (isAnimatedComplete p R)

def animatedCompleteInclusion : CompleteAnimatedAlgebra p R ⟶ AnimatedAlgebra R :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (isAnimatedComplete p R)).ι

instance : Quasicategory (CompleteAnimatedAlgebra p R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

abbrev reductionShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1,0}).obj (nerve (ℕᵒᵖ))

/-- n 番目は R ← R[t] → R、評価値は p^(n+1) と 0。
大きい指数から小さい指数への射は t ↦ p^(n−m)t。 -/
def primePowerSpans : ℕᵒᵖ ⥤ (Limits.WalkingSpan ⥤ PerfectoidizationInterface.A_R R) := by
  let eval (a : R) : PerfectoidizationInterface.ofAlgebra R (Polynomial R) ⟶
      PerfectoidizationInterface.ofAlgebra R R :=
    Under.homMk (CommRingCat.ofHom (Polynomial.evalRingHom a)) (by
      ext x
      change Polynomial.eval a (Polynomial.C x) = x
      simp)
  exact {
    obj := fun n => Limits.span (eval ((p : R) ^ (n.unop + 1))) (eval 0)
    map := fun {n m} f => Limits.spanHomMk
      (Under.homMk (CommRingCat.ofHom (Polynomial.eval₂RingHom Polynomial.C
        (Polynomial.C ((p : R) ^ (n.unop - m.unop)) * Polynomial.X))) (by
        ext x
        change Polynomial.eval₂ Polynomial.C
          (Polynomial.C ((p : R) ^ (n.unop - m.unop)) * Polynomial.X) (Polynomial.C x) = Polynomial.C x
        simp))
      (𝟙 _) (𝟙 _) (by sorry) (by sorry) -- f.unop : m ≤ n、二つの評価写像との両立
    map_id := by sorry -- t ↦ t
    map_comp := by sorry -- 指数差の和と積の冪
  }

def discreteTowerDiagram (F : ℕᵒᵖ ⥤ PerfectoidizationInterface.A_R R) :
    reductionShape.{u} ⟶ nerve (PerfectoidizationInterface.A_R R) where
  app n := ↾fun x => (F.mapComposableArrows _).obj x.down
  naturality := by sorry -- 順序射の合成を F で送る

/-- 二つの離散塔の自然変換の nerve。評価は元の自然変換の成分。 -/
def discreteTowerMap {F G : ℕᵒᵖ ⥤ PerfectoidizationInterface.A_R R} (α : F ⟶ G) :
    ((ihom reductionShape).obj (nerve (PerfectoidizationInterface.A_R R))).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discreteTowerDiagram R F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discreteTowerDiagram R G)) :=
  Classical.choose (show ∃ e : ((ihom reductionShape).obj (nerve (PerfectoidizationInterface.A_R R))).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discreteTowerDiagram R F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (discreteTowerDiagram R G)),
    ∀ n : ℕᵒᵖ, (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)))).edge =
      (nerve.edgeMk (α.app n)).edge from by
    sorry) -- α の自然性の四角形を含む nerve の辺。ULift は添字だけに置く

/-- 上の普通の span を離散埋め込みで送り、塔の圏で押し出す。
次に定数塔 X と二項余積を取る。第 n 項は X ⊗^L_ℤ ℤ/p^(n+1)。 -/
def animatedReductionTower (X : (AnimatedAlgebra R) _⦋0⦌) : reductionShape.{u} ⟶ AnimatedAlgebra R := by
  let spans := (primePowerSpans p R).flip
  let span := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan (discreteTowerMap R (spans.map Limits.WalkingSpan.Hom.fst)).toTruncated
    (discreteTowerMap R (spans.map Limits.WalkingSpan.Hom.snd)).toTruncated ≫
    (ihom reductionShape).map (discreteToAnimated R)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit span := by sorry -- 塔の圏での点ごとの導来押し出し
  let D := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := reductionShape) X)) hc.choose.vertex
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D := by sorry -- animated R 代数の二項余積は R 上の導来テンソル
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm hd.choose.vertex

/-- 概要：animated R 代数の導来 p 完備化（反射的局所化、代数構造と両立）。
方針：D(R) の完備化（DerivedGeneral/CompletionFunctor）と底の加群で比較する。W9 続き 6 の補記：animated 圏での
構成も記す——単体的可換環としての導来 mod p^n の逆極限（π_0 の商の遷移が全射なのでその lim¹ が消え、 animated 圏に留まる）、底の加群で完備性を判定し、完備対象への反射
という普遍性で特徴づける。
規約：`AnimatedAlgebra R ⟶ CompleteAnimatedAlgebra R` と単位。
使われ方：完備テンソル S_1 ⊗̂^L_{S_3} S_2。 -/
def animatedReflection :
    Σ L : AnimatedAlgebra R ⟶ CompleteAnimatedAlgebra p R,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L (animatedCompleteInclusion p R) := by
  sorry -- X ⊗^L_ℤ ℤ/p^(n+1) の逆極限。π₀ の商は全射系なのでその lim¹ は零。
        -- 底の導来加群で完備性を検出し、完備代数への写像の普遍性を単位・余単位に移す

def animatedCompletion : AnimatedAlgebra R ⟶ CompleteAnimatedAlgebra p R :=
  (animatedReflection p R).1

theorem animatedCompletion_limit (X : (AnimatedAlgebra R) _⦋0⦌) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (animatedReductionTower p R X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧
      c.vertex = (animatedCompletion p R ≫ animatedCompleteInclusion p R).app _ X := by
  sorry -- π₀(X)/p^(n+1) の射は全射。この系の lim¹ が消えて逆極限は連結、反射の頂点へ極限錐を移送

def animatedCompletionUnit :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (AnimatedAlgebra R)) (animatedCompletion p R ≫ animatedCompleteInclusion p R) :=
  (animatedReflection p R).2.unitHom

/-- 概要：導来 p 完備な離散 R 代数は `discreteToAnimated`（A2-1）で `CompleteAnimatedAlgebra` に入る。
方針：離散環の底は離散加群。
規約：—
使われ方：離散版との一致。 -/
theorem discreteToAnimated_complete (S : PerfectoidizationInterface.C_R R p) :
    isAnimatedComplete p R ((discreteToAnimated R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S.obj)) := by
  sorry -- S.property は離散 S 加群 S の p 完備性。R へ制限しても導来 mod p^n の塔は同じ

def completeDiscreteToAnimated :
    nerve (PerfectoidizationInterface.C_R R p) ⟶ CompleteAnimatedAlgebra p R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (nerveMap (PerfectoidizationInterface.completeInclusion R p) ≫ discreteToAnimated R)
    (by
      intro x
      obtain ⟨S, rfl⟩ := nerveEquiv.symm.surjective x
      change isAnimatedComplete p R ((discreteToAnimated R).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S.obj))
      exact discreteToAnimated_complete p R S)

end SerrePositivity.BhattScholze.Perfectoidization.Derived
