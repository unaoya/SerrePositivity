-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.UniversalProperty（仮。原典 Cor 8.14 と E3 の欄 universal）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.3、単位 A7-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryFirstPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom
-- 本ファイルは drafts/A7/{AnimatedDomain,DiscreteCore,AnimatedPerfectoidization}.lean、drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A5/{PerfectSiteComparison,SemiperfectoidCase}.lean を import する。
-- G-A7-5 の芯は drafts/A7/DiscreteCore.lean に切り出した（W9-II-24：A5 が import するので本ファイルには置けない）。

/-!
# 離散な場合の普遍性（BS 著者版 Cor 8.14）と E3 の欄 `universal`

## 概要
S_perfd が離散なら S_perfd は perfectoid 環で、S → S_perfd は perfectoid 環への普遍な写像（`IsPerfectoidization`）。E3 の欄は任意の離散 S
（非完備も）について `IsTheoryDiscrete R (e3Perfd S) → IsPerfectoidization p (unit S)` で、S^∧ 経由（D41）。

## 方針
芯 G-A7-5（A5-2 と共有、drafts/A7/DiscreteCore.lean）：S_perfd 離散 ⇒ Δ_perf 離散（d 進 Nakayama）⇒ 完全 p 完備 δ 環（A4）⇒ 完全 prism ⇒ S_perfd perfectoid（Thm 3.10）。
普遍性：存在は比較写像の脚（A5-1）、一意性は原典：g_1, g_2 が S 上で一致 ⇒ η = (g_1, g_2) : X := S_perfd ⊗̂^L_S S_perfd → S′ は
X_perfd ≃ S_perfd（Prop 8.13、T perfectoid ⇒ T_perfd = T）を通り乗法で因数分解 ⇒ g_1 = g_2。乗法との一致には単位の整合性 F(η_S) = η_P（G-A7-8、
A5 の極限の脚から。W9-II-23：単位の自然性だけでは不足）を先に示す。

## 規約
S 離散。離散な環の間の animated／E∞ 代数の射は環準同型（`discreteToAnimated_fullyFaithful`）。

## 使われ方
`TheoryPerfectoidizationInterface.universal`（A9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
/-- 完備な離散入力における A4 の直接の単位を H⁰ で読む。
P の R 代数構造と η : S → P は同じ CAlg の射から来る。 -/
abbrev perfdValue (S : A_R R) := (perfectoidizationFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S)
abbrev perfdRing (S : A_R R) := cAlgH0Algebra (E := E) R (perfdValue (E := E) p R hR S)

def discretePerfdUnit (S : A_R R) : S ⟶ perfdRing (E := E) p R hR S :=
  (discreteToH0 (E := E) R S).hom ≫ (cAlgH0OnHomotopy (E := E) R).map
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S))

/-- 指定された離散表示。H⁰ による同定が恒等になる向きを選ぶ。 -/
def discretePerfdIso (S : A_R R) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S)) :
    { e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfdValue (E := E) p R hR S)
        ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (perfdRing (E := E) p R hR S))) //
      (cAlgH0OnHomotopy (E := E) R).map e.hom = (discreteToH0 (E := E) R (perfdRing (E := E) p R hR S)).hom } := by
  sorry -- 離散表示を H⁰ の標準同型で補正し、H⁰ が恒等となる表示を得る

/-! ## G-A7-3：perfectoid の perfd -/

/-- 概要：T perfectoid（R 代数）なら T → T_perfd は同値（CAlg_R）、よって (T_perfd)_perfd ≃ T_perfd（T_perfd perfectoid のとき）。
方針：T は semiperfectoid で普遍 perfectoid 化は T 自身、A5-2 `perfectoidization_semiperfectoid_iso`。
規約：—
使われ方：Cor 8.14 の一意性。 -/
theorem perfectoidization_of_perfectoid (T : Type u) [CommRing T] [Algebra R T] (hT : IsIntegralPerfectoid T p) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R T))) := by
  sorry -- A5-2 perfectoidization_semiperfectoid_iso。T の普遍 perfectoid 化は恒等射

/-! ## Cor 8.14 後半：普遍性 -/

/-- 概要：存在：perfectoid S′ と S → S′ に対し S_perfd → S′（S の下）：比較写像の脚 Δ_{S,perf} → B_{S′}（A5-1 `perfectionComparisonLeg`）の mod d。
方針：A5-1。
規約：環準同型（両者離散）。
使われ方：`IsPerfectoidization` の存在部分。 -/
theorem exists_extension_of_perfectoid (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj))
    (T : Type u) [CommRing T] (hT : IsIntegralPerfectoid T p) (f : S.obj.right →+* T) :
    ∃ g : (perfdRing (E := E) p R hR S.obj).right →+* T,
      g.comp (discretePerfdUnit (E := E) p R hR S.obj).right.hom = f := by
  sorry -- f が定める完全 prism への perfectionComparisonLeg の mod d を H⁰ で読む

/-- 概要：G-A7-8（W9-II-23）：単位の整合性。P := S_perfd が離散（よって perfectoid、DiscreteCore）のとき F(η_S) = η_P : P → P_perfd（F = perfd）。
方針：A5-1 の極限表示 P = lim_{Perfd_{S/}} O の脚 λ_f : P → T（f : S → T）。f = η_S の脚を q : P → P とすると、任意の f について λ_f は添字圏の射
(P, η_S) → (T, f) なので錐の可換性から λ_f ∘ q = λ_f、P・T は離散で脚は射を識別する（極限は環の極限）ので q = id_P。極限比較の S に関する自然性と η_P の可逆性
（`perfectoidization_of_perfectoid`）から η_P^{-1} ∘ F(η_S) = q = id_P。Cor 8.14 の一意性は使わない（循環なし）。単位の自然性だけでは「S 上で一致」までしか出ない。
規約：—
使われ方：`selfTensor_unit_eq_mul`。 -/
theorem perfectoidization_map_unit_eq_unit (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    let P := perfdRing (E := E) p R hR S.obj
    let F := perfectoidizationFunctor (E := E) p R hR
    let η := discretePerfdUnit (E := E) p R hR S.obj
    (discretePerfdIso (E := E) p R hR S.obj h).1.inv ≫
        SSet.Truncated.HomotopyCategory.homMk (((nerve.edgeMk η).map F).toTruncated) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex P) := by
  sorry -- 比較の脚 λ_f に対し λ_f ∘ λ_η = λ_f。離散な極限の脚が射を識別して q=λ_η=id。
        -- A5 の比較の自然性と η_P の可逆性で移す（Cor 8.14 の一意性は用いない）

/-- 左右とも同じ指定単位 S → H⁰(FS) の完備 animated 押し出し。 -/
def completePerfdRing (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) : C_R R p :=
  ⟨perfdRing (E := E) p R hR S.obj, by
    sorry⟩ -- G-A7-5 で perfectoid、従って底の環は導来 p 完備

def selfTensorSpan (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    TensorSpan (CompleteAnimatedAlgebra p R) :=
  let η : S ⟶ completePerfdRing (E := E) p R hR S h := ObjectProperty.homMk (discretePerfdUnit (E := E) p R hR S.obj)
  let f := (nerve.edgeMk η).map (completeDiscreteToAnimated p R)
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f.toTruncated f.toTruncated

abbrev selfTensorObj (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :=
  (completeAnimatedPushout p R (selfTensorSpan (E := E) p R hR S h)).1.vertex

abbrev selfTensorFactor (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :=
  (completeDiscreteToAnimated p R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (completePerfdRing (E := E) p R hR S h))

/-- i=0,1 は span の頂点 1,2 での同じ余錐の脚。 -/
def selfTensorLeg (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) (i : Fin 2) :
    (CompleteAnimatedAlgebra p R).Edge (selfTensorFactor (E := E) p R hR S h) (selfTensorObj (E := E) p R hR S h) := by
  let v : (horn 2 0 : SSet.{u+1}) _⦋0⦌ :=
    ⟨stdSimplex.obj₀Equiv.symm i.succ, by sorry⟩ -- 各頂点はホーンに含まれる
  let c := (completeAnimatedPushout p R (selfTensorSpan (E := E) p R hR S h)).1
  convert _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c v using 1 <;>
    sorry -- i=0,1 について edgeSpan_left・edgeSpan_right の終点を読む

abbrev hoEdge {V : SSet.{u+1}} {x y : V _⦋0⦌} (e : V.Edge x y) :=
  SSet.HomotopyCategory.homMk e

/-- (id_P,id_P) から来る乗法。標的 P は離散なので二脚上の等式がこの射を決める。 -/
def selfTensorMul (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    let X := selfTensorObj (E := E) p R hR S h
    let P := selfTensorFactor (E := E) p R hR S h
    { m : (HomotopyCategory.mk X : hoFunctor.obj (CompleteAnimatedAlgebra p R)) ⟶ HomotopyCategory.mk P //
      ∀ i, hoEdge (selfTensorLeg (E := E) p R hR S h i) ≫ m = 𝟙 _ } := by
  sorry -- 指定単位二本への恒等な整合をもつ余錐から押し出しの普遍性で降ろす

/-- A2 の Fil₀ の始域。Poly_R の離散 E∞ 代数値の関手を sifted 延長し、
導来 p 完備入力に制限する。非離散の X の単位もこの CAlg_R で評価する。 -/
def animatedRealization : AnimatedAlgebra R ⟶ E.CAlg R :=
  Classical.choose (show ∃ G : AnimatedAlgebra R ⟶ E.CAlg R,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (polyYoneda R ≫ G) (polynomialDiscreteDiagram R ≫ E.discrete R)) from by
    sorry) -- 要確認：A2 の hodgeTateUnitCAlg の始域。多項式代数の E∞ 実現を sifted 延長

def animatedUnderlyingCAlg : CompleteAnimatedAlgebra p R ⟶ E.CAlg R :=
  animatedCompleteInclusion p R ≫ animatedRealization (E := E) R

def animatedPerfdUnit (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (animatedUnderlyingCAlg (E := E) p R) (perfectoidizationAnimated (E := E) p R hR) := by
  let P := perfectPrism p R hR
  let modD := modPrismFunctor (E := E) p R hR
  let fil₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (animatedUnderlyingCAlg (E := E) p R) (animatedDeltaUnderlying (E := E) p R hR ≫ modD) := by
    sorry -- 要確認：A2 の hodgeTateUnitCAlg の完備 animated 入力への制限
  let toCompletion := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (animatedFrobeniusColimit (E := E) p R hR)
    (prismCAlgCompletionUnit (E := E) (p := p) P)
  exact fil₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.postcomposeFunctorHom modD (animatedTowerLeg (E := E) p R hR ≫ toCompletion)

/-- 完備な離散代数の実現は通常の離散 CAlg と自然に同型。 -/
def completeRealizationDiscreteIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (completeDiscreteToAnimated p R ≫ animatedUnderlyingCAlg (E := E) p R)
      (nerveMap (completeInclusion R p) ≫ E.discrete R) := by
  sorry -- 多項式分解の幾何学的実現は元の離散代数を表す

theorem animatedPerfdUnit_discrete (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (completeDiscreteToAnimated p R) (animatedPerfdUnit (E := E) p R hR) ≫
        (perfectoidizationAnimated_discrete (E := E) p R hR).hom =
      (completeRealizationDiscreteIso (E := E) p R).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom
        (nerveMap (completeInclusion R p)) (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR) := by
  sorry -- A2 の Fil₀ と A4 の同じ第0脚を離散入力に制限した自然性

/-- 概要：X := S_perfd ⊗̂^L_S S_perfd（`CompleteAnimatedAlgebra`）の perfd は S_perfd：Prop 8.13（S_1 = S_2 = S_perfd、S_3 = S）と
(S_perfd)_perfd ≃ S_perfd（`perfectoidization_of_perfectoid`）。単位 X → X_perfd とこの同値の合成は乗法 m : X → S_perfd（紙 3）。
方針（W9-II-23）：Prop 8.13 の比較 F(P) ⊗̂_{F(S)} F(P) → F(X) の二つの脚は F(i_1)・F(i_2)。`perfectoidization_map_unit_eq_unit` と η_P の逆で左辺を P ⊗̂_P P ≃ P と
同一視し、逆向きを e : F(X) → P とすると、単位の自然性から e ∘ η_X ∘ i_j = e ∘ F(i_j) ∘ η_P = id_P、押し出しの普遍性（G-A7-6）で e ∘ η_X = m。
A7-1 `perfectoidization_relativeTensor`。
規約：—
使われ方：一意性。 -/
def selfTensor_perfectoidization_eq (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    let X := selfTensorObj (E := E) p R hR S h
    let P := selfTensorFactor (E := E) p R hR S h
    let F := perfectoidizationAnimated (E := E) p R hR
    { e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.app _ X) ((animatedUnderlyingCAlg (E := E) p R).app _ P) //
      ∀ i, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (animatedPerfdUnit (E := E) p R hR) P ≫
        hoEdge ((selfTensorLeg (E := E) p R hR S h i).map F) ≫ e.hom = 𝟙 _ } := by
  sorry -- Prop 8.13 の二脚は F(i_j)。G-A7-8 と η_P の逆で P ⊗̂_P P ≃ P に移し、比較の逆から e を取る

theorem selfTensor_unit_eq_mul (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (animatedPerfdUnit (E := E) p R hR) (selfTensorObj (E := E) p R hR S h) ≫
        (selfTensor_perfectoidization_eq (E := E) p R hR S h).1.hom =
      (hoFunctor.map (animatedUnderlyingCAlg (E := E) p R)).toFunctor.map (selfTensorMul (E := E) p R hR S h).1 := by
  sorry -- 単位の自然性と e の両脚上の式で、双方の i_j 制限は恒等。
        -- P は離散なので X→P は π₀X→P で判定でき、押し出しの普遍性で一致する

/-- 概要：一意性：g_1, g_2 : S_perfd → S′（S′ perfectoid）が S 上で一致すれば g_1 = g_2。
方針：η := (g_1, g_2) : X → S′（押し出しの普遍性、G-A7-6）。S′ perfectoid なので η は X → X_perfd → S′_perfd ≃ S′ を通り、`selfTensor_unit_eq_mul` で
η = g ∘ m。g_i = η ∘ i_i = g。離散な標的なので π_0 Map = Hom（`discreteToAnimated_fullyFaithful`）。
規約：—
使われ方：`IsPerfectoidization` の一意性部分。 -/
theorem extension_unique_of_perfectoid (S : C_R R p) (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj))
    (T : Type u) [CommRing T] (hT : IsIntegralPerfectoid T p)
    (g₁ g₂ : (perfdRing (E := E) p R hR S.obj).right →+* T)
    (heq : g₁.comp (discretePerfdUnit (E := E) p R hR S.obj).right.hom =
      g₂.comp (discretePerfdUnit (E := E) p R hR S.obj).right.hom) : g₁ = g₂ := by
  sorry -- (g₁,g₂) が誘導する X→T は η_X を通る。selfTensor_unit_eq_mul で乗法を通り、
        -- 離散標的への Map は 0 切り捨て（Hom(π₀X,T)）なので両脚は同じ環準同型

/-- 概要：Cor 8.14：S_perfd 離散 ⇒ `IsPerfectoidization p (S → S_perfd)`。
方針：`perfectoidization_isIntegralPerfectoid_of_discrete`、`exists_extension_of_perfectoid`、`extension_unique_of_perfectoid`。
規約：S は導来 p 完備な離散 R 代数。
使われ方：`e3Universal`。 -/
theorem perfectoidization_isPerfectoidization_of_discrete (S : C_R R p)
    (h : IsTheoryDiscrete (E := E) R (perfdValue (E := E) p R hR S.obj)) :
    IsPerfectoidization p (discretePerfdUnit (E := E) p R hR S.obj).right.hom := by
  sorry -- G-A7-5 を perfectoidizationFunctor_vertex で移送。存在の脚と extension_unique_of_perfectoid

/-! ## E3 の欄 -/

/-- 概要：E3 の `universal`：任意の離散 S について、`e3Perfd S` が離散なら `IsPerfectoidization p (e3H0RingData.unit.app S)`。
方針：S^∧ に Cor 8.14（`e3Perfd_of_complete`・`e3Unit_of_complete`・`e3H0_of_complete`、A4-3）。perfectoid 環は p 完備なので S → T は S^∧ → T を
一意に通る（`completionRing` の普遍性、Interface.lean:237、G-A7-7）。
規約：`TheoryPerfectoidizationInterface.universal` の型そのまま。
使われ方：A9。 -/
theorem e3Universal (hR : IsIntegralPerfectoid R p := by assumption) (S : A_R R) (hS : IsTheoryDiscrete (E := E) R ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S))) :
    IsPerfectoidization p ((e3H0RingData (E := E) p R hR).unit.app S).right.hom := by
  sorry -- S^∧ に Cor 8.14。e3Perfd_of_complete・e3Unit_of_complete・e3H0_of_complete
        -- で離散性・単位・H⁰ を読み替え、completion_existsUnique で S→T の存在一意性を戻す

end SerrePositivity.BhattScholze.Perfectoidization.Derived
