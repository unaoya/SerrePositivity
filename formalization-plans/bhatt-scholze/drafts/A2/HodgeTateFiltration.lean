-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.HodgeTateFiltration（仮。原典 Construction 7.6 の HT filtration）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.3、単位 A2-3。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.HeartFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Stability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Loop
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareHom

-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology}.lean、drafts/DerivedGeneral/Truncation.lean、
-- drafts/A1/HodgeTateComparison.lean（Thm 6.3）、drafts/Shared/DeRhamPolynomial.lean、drafts/A7/AnimatedDomain.lean を import する。

/-!
# Hodge–Tate filtration と導来外冪つき余接複体（BS 著者版 Construction 7.6 の第二段落）

## 概要
Δ̄_R := Δ_R ⊗^L_A A/d（D(A/d) 値、E∞ 構造は忘れる）に、exhaustive な増大 ℕ 添字の filtration Fil_i Δ̄_R を、多項式代数上の Postnikov 切り捨て
τ^{≤i} Δ̄_P の左 Kan 延長として定める。次数商 gr^i は Ω^i_{P/k}[−i] の左 Kan 延長で、これを (∧^i L_{R/k})^∧[−i]（導来外冪つき余接複体の
p 完備化の −i shift）の**定義**とする（D33。Illusie の単体的分解による定義と一致）。原典の「HT 比較 for Δ̄_R」は、この gr の同一視
（多項式代数上の Thm 6.3）。

## 方針
Kan 延長（sifted 余極限保存な延長、HTT 5.5.8.15）は cofiber と余極限と交換するので、filtration・gr・exhaustive 性は Poly 上の性質から従う。
D(A/d) の p 完備な部分圏で述べる（E∞ 構造つきの filtration は A4 以降で要れば足す）。

## 規約
捻り {−i} は向き付きなので落とす（D28）。多項式代数上では Δ̄_P ∈ D^{[0,n]}（Thm 6.3）なので Fil_n = Δ̄_P。

## 使われ方
A2-4（完備化不変性・テンソルの gr による証明）、A4（Lemma 8.4：P⁰ の議論は別だが、Example 8.3 で gr を使う）、A5（Prop 8.5：S 半完全 perfectoid なら
L_{S/Z_p}[−1] 連結 ⇒ Δ_S 連結）、A7（Prop 8.13：gr の Künneth）、A8（Thm 10.11 の Lemma 10.12）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.Perfectoidization.Derived
attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## 多項式代数上の切り捨て -/

abbrev CompleteD (p : ℕ) (k : Type u) [CommRing k] : SSet.{u+1} :=
  fullSubcomplexOnVertices (derivedInfinityCategory k) (completeAt (p : k))

instance (k : Type u) [CommRing k] : Quasicategory (CompleteD p k) :=
  fullSubcomplexOnVertices_quasicategory _ _

def completeDInclusion (p : ℕ) (k : Type u) [CommRing k] : CompleteD p k ⟶ derivedInfinityCategory k :=
  (fullSubcomplexOnVertices _ (completeAt (p : k))).ι

def pCompletionReflection (p : ℕ) (k : Type u) [CommRing k] :
    Σ L : derivedInfinityCategory k ⟶ CompleteD p k, QCatAdjunction L (completeDInclusion p k) := by
  sorry -- 要確認：DerivedGeneral/CompletionFunctor へ。主元 p の反射の単位・余単位。completion の p, d が明示引数になった段階で (p,0) に特殊化する。

def pCompletionUnit (p : ℕ) (k : Type u) [CommRing k] :
    FunctorHom (𝟙 (derivedInfinityCategory k)) ((pCompletionReflection p k).1 ≫ completeDInclusion p k) :=
  (pCompletionReflection p k).2.unitHom

theorem completeD_siftedColimits (p : ℕ) (k : Type u) [CommRing k] :
    HasSmallSiftedColimits (CompleteD p k) := by
  sorry -- D(k) の sifted 余極限を反射し、随伴で完備対象への余錐を判定する

def completeModuleLan (p : ℕ) (k : Type u) [CommRing k]
    (F : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ derivedInfinityCategory k) :
    AnimatedAlgebra k ⟶ CompleteD p k :=
  siftedLan k (completeD_siftedColimits p k)
    (F ≫ (pCompletionReflection p k).1)

/-- 概要：Δ̄_0(P) := Δ_0(P) ⊗^L_A A/d を **D(k) 値**（k = A/d）で（W9-I-36：Fil と gr の値の圏に合わせる。D(A) 値は忘却で）。
方針：`derivedPrismaticCohomologyDerived` と底変換 D(A) → D(k)（⊗^L_A A/d は k 加群構造をもつ）。
規約：D(k) の頂点。D(A) 値の版は `Res_A` を後合成。
使われ方：Postnikov 切り捨ての入力。 -/
def hodgeTatePoly (hP : IsBoundedPrism P) : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory (A ⧸ P.ideal) :=
  polyUnderlying (E := E) P hP ≫ prismModIdeal (E := E) P ≫ E.forget _

/-- 概要：Poly 上の τ^{≤i} Δ̄_0（i : ℕ）、関手的。
方針：DerivedGeneral/Truncation の `truncationLE A i` を後合成。
規約：i について増大（τ^{≤i} → τ^{≤i+1}）。
使われ方：Fil_i の Kan 延長の入力。 -/
def hodgeTatePolyTruncated (hP : IsBoundedPrism P) (i : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory (A ⧸ P.ideal) :=
  hodgeTatePoly (E := E) P hP ≫ Derived.truncationLE (A ⧸ P.ideal) i

/-- 概要：Poly 上で Δ̄_P ∈ D^{[0,n]}（n = 変数の個数）なので τ^{≤n} Δ̄_P ≃ Δ̄_P。
方針：Thm 6.3（H^i = 0 for i > n）と `truncationLE_of_isConnective`（W9-III-11 で改名）。
規約：—
使われ方：exhaustive 性。 -/
theorem hodgeTatePoly_bounded (n : ℕ) :
    let k := A ⧸ P.ideal
    let x := (hodgeTatePoly (E := E) P hP).app _ (ULift.up (nerveVertex (⟨n⟩ : Poly k)))
    Derived.IsCoconnectiveAt k 0 x ∧ Derived.IsConnectiveAt k n x ∧
      Nonempty (VertexIso ((Derived.truncationLE k n).app _ x) x) := by
  sorry -- Thm 6.3。i<0 および i>n のコホモロジーが零なので切り捨ての余単位が可逆

/-! ## Kan 延長 -/

/-- 概要：HT filtration Fil_i Δ̄ : P_Σ(N(Poly k)) → D(k)_{p-comp}（k = A/d）、τ^{≤i} Δ̄_0 の**完備圏内の** sifted 余極限保存な延長
（= LΛ_p ∘ Lan。W9-I-26：D(A) で延長すると p 完備性が失われ Fil_0 ≠ R^∧）。
方針：A2-1 の `exists_siftedExtension` を完備圏（または D(k) で延長して `completion`（DerivedGeneral/CompletionFunctor）を後合成）。
規約：値は導来 p 完備な D(k) の対象（`IsDerivedComplete`）。D(A) へは忘却。
使われ方：以下。 -/
def hodgeTateFiltration (hP : IsBoundedPrism P) (i : ℕ) :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ CompleteD p (A ⧸ P.ideal) :=
  completeModuleLan p _ (hodgeTatePolyTruncated (E := E) P hP i)

abbrev reducedDelta (hP : IsBoundedPrism P) := deltaUnderlying (E := E) P hP ≫ prismModIdeal (E := E) P
def reducedDeltaComplete (hP : IsBoundedPrism P) :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ CompleteD p (A ⧸ P.ideal) :=
  fullSubcomplexLift _ (reducedDelta (E := E) P hP ≫ E.forget _) (by
    sorry) -- (p,d) 完備な Δ の導来 mod d は p 完備

abbrev filtrationShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1,0}).obj (nerve ℕ)
abbrev filtrationIndex (i : ℕ) : filtrationShape.{u} _⦋0⦌ := ULift.up (nerveVertex i)

/-- 各段の指定、増大列、および Δ̄ への増大余錐を一緒に持つ。
多項式上で第 i 脚は H^{≤i} の同型を与えるため、切り捨ての余単位を表す。 -/
structure HTTower (hP : IsBoundedPrism P) where
  diagram : filtrationShape ⟶ (ihom (AnimatedAlgebra (A ⧸ P.ideal))).obj (CompleteD p (A ⧸ P.ideal))
  level (i : ℕ) : diagram.app _ (filtrationIndex i) = functorVertex (hodgeTateFiltration (E := E) P hP i)
  augmentation : JoinCocone diagram
  target : augmentation.vertex = functorVertex (reducedDeltaComplete (E := E) P hP)
  truncates (Q : Poly (A ⧸ P.ideal)) (i : ℕ) (j : ℤ) (hj : j ≤ i) :
    let x := (polyYoneda _).app _ (ULift.up (nerveVertex Q))
    let e := (mapJoinCocone (evaluateFunctorAt x ≫ completeDInclusion p _) augmentation).leg
      (SSet.yonedaEquiv.symm (filtrationIndex i))
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ P.ideal)) j).map
      ((derivedInfinityHomotopyEquivalence _).functor.map (SSet.Truncated.HomotopyCategory.homMk e)))

def hodgeTateTower (hP : IsBoundedPrism P) : HTTower (E := E) P hP := by
  sorry -- 要確認：DerivedGeneral/Truncation へ。τ≤i の増大列と余単位を Poly 上で取り、
        -- 完備圏の sifted 延長の関手圏同値で余錐ごと延長する

/-- 第 i 段から次段への射。augmentation の i 番目の脚が Fil_i → Δ̄。 -/
def hodgeTateFiltration_step (hP : IsBoundedPrism P) (i : ℕ) :
    FunctorHom (hodgeTateFiltration (E := E) P hP i) (hodgeTateFiltration (E := E) P hP (i+1)) := by
  let T := hodgeTateTower (E := E) P hP
  let e := (uliftEdge.{0,u+1} (nerve.edgeMk (homOfLE (Nat.le_succ i))).toTruncated).map ((truncation 2).map T.diagram)
  exact eqToHom (congrArg HomotopyCategory.mk (T.level i).symm) ≫
    SSet.Truncated.HomotopyCategory.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk (T.level (i+1)))

def hodgeTateAugmentation (hP : IsBoundedPrism P) (i : ℕ) :
    FunctorHom (hodgeTateFiltration (E := E) P hP i) (reducedDeltaComplete (E := E) P hP) := by
  let T := hodgeTateTower (E := E) P hP
  let e := T.augmentation.leg (SSet.yonedaEquiv.symm (filtrationIndex i))
  exact eqToHom (by simpa using congrArg HomotopyCategory.mk (T.level i).symm) ≫
    SSet.Truncated.HomotopyCategory.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk T.target)

/-- D4-01。多項式上の通常の外微分形式。f は dX_j を d(f(X_j)) に送る。 -/
def polyFormsModule (k : Type u) [CommRing k] (i : ℕ) : Poly k ⥤ ModuleCat.{u} k where
  obj Q := ModuleCat.of k (SerrePositivity.DeRham.forms k (Fin Q.n) i)
  map {Q Q'} f := by
    sorry -- a dX₁∧…∧dXᵢ ↦ f(a) d(fX₁)∧…∧d(fXᵢ)、Shared の外積と線形性
  map_id := by sorry -- 自由基底上で恒等
  map_comp := by sorry -- 微分と代入の連鎖律

/-- discreteEmbedding の加群から先の部分を使い、通常の形式を次数零に入れる。 -/
def ordinaryFormsDiagram (k : Type u) [CommRing k] (i : ℕ) :
    (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ derivedInfinityCategory k := by
  let F := polyFormsModule k i ⋙ moduleSemifreeResolutionFunctor k
  let N : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ nerve _ :=
    { app := fun n => ↾fun x => (F.mapComposableArrows _).obj x.down
      naturality := by sorry } -- 射列の制限と F の合成
  exact N ≫ closedNerveInclusion k (Semifree k)

/-- D33。任意の k に対し LΛ_p∘Lan(Ω^i) を完備圏で取る。 -/
def cotangentWedgeGeneral (p : ℕ) (k : Type u) [CommRing k] (i : ℕ) :=
  completeModuleLan p k (ordinaryFormsDiagram k i) ≫ completeDInclusion p k

def cotangentWedge (i : ℕ) := cotangentWedgeGeneral p (A ⧸ P.ideal) i

/-- 離散 S での値は S 加群。k へ係数制限すると上の k 加群を回収する（W9-I-36）。 -/
def cotangentWedgeAtAlgebra (p : ℕ) (k S : Type u) [CommRing k] [CommRing S] [Algebra k S] (i : ℕ) :
    Σ M : (CompleteD p S) _⦋0⦌, VertexIso
      ((completeDInclusion p S ≫ derivedInfinityRestrictScalars (E := E) (algebraMap k S)).app _ M)
      ((discreteToAnimated k ≫ cotangentWedgeGeneral p k i).app _
        (nerveVertex (PerfectoidizationInterface.ofAlgebra k S))) := by
  sorry -- 多項式分解の各段の Ω^i を S 上に引き戻し、その S 加群の実現を導来 p 完備化

/-- D4-01 の有界な場合。一般の k では左辺を使う。 -/
theorem polyForms_boundedComparison (hP : IsBoundedPrism P) (n i : ℕ) :
    let k := A ⧸ P.ideal
    let F := ordinaryFormsDiagram k i ≫ (pCompletionReflection p k).1 ≫ completeDInclusion p k
    Nonempty (VertexIso (F.app _ (ULift.up (nerveVertex (⟨n⟩ : Poly k))))
      (moduleHeartVertex k (ModuleCat.of k (SerrePositivity.DeRham.completedForms k (Fin n) p i)))) := by
  sorry -- 要確認：Shared の completedForms_eq_derivedCompletion_of_boundedTorsion 待ち。
        -- hP より k=A/d の p 冪ねじれが有界。多項式形式は有限自由

/-- 向きで捻りを同定したあとの cohomological shift [−i]。 -/
def formShift (k : Type u) [CommRing k] : ℕ → (derivedInfinityCategory k ⟶ derivedInfinityCategory k)
  | 0 => 𝟙 _
  | i+1 => formShift k i ≫ loopFunctor _

/-- 0 段は Fil₀、後続段は指定した遷移の cofiber。関手圏での四角形により自然性を含める。 -/
def IsGradedTerm {K D : SSet.{u+1}} [Quasicategory D] (L : ℕ → (K ⟶ D))
    (step : ∀ i, FunctorHom (L i) (L (i+1))) (i : ℕ) (W : K ⟶ D) : Prop :=
  match i with
  | 0 => Nonempty (FunctorIso (L 0) W)
  | j+1 =>
    ∃ e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj D))
        (functorVertex (L j)) (functorVertex (L (j+1))),
      SSet.Truncated.HomotopyCategory.homMk e = step j ∧
        ∃ c : CofiberSquare e, Nonempty (VertexIso c.cofiber (functorVertex W))

abbrev filtrationUnderlying (hP : IsBoundedPrism P) (i : ℕ) :=
  hodgeTateFiltration (E := E) P hP i ≫ completeDInclusion p _

def polyTruncationIso (hP : IsBoundedPrism P) (i : ℕ) :
    FunctorIso (polyYoneda _ ≫ filtrationUnderlying (E := E) P hP i) (hodgeTatePolyTruncated (E := E) P hP i) := by
  sorry -- siftedLanIso と、p 完備な切り捨てにおける反射の単位の同型

def polyTruncationStep (hP : IsBoundedPrism P) (i : ℕ) :=
  (polyTruncationIso (E := E) P hP i).inv ≫ F2.Presentable.precomposeFunctorHom (polyYoneda _)
    (F2.Presentable.postcomposeFunctorHom (completeDInclusion p _) (hodgeTateFiltration_step (E := E) P hP i)) ≫
    (polyTruncationIso (E := E) P hP (i+1)).hom

/-- 多項式上の gr は LΛ_p Ω^i[−i]。Thm 6.3 の Ω̂^i から D4-01 で移す。 -/
theorem hodgeTatePoly_gr (i : ℕ) :
    let k := A ⧸ P.ideal
    let Ω := ordinaryFormsDiagram k i ≫ (pCompletionReflection p k).1 ≫ completeDInclusion p k
    Nonempty (FunctorIso (polyYoneda k ≫ cotangentWedge P i) Ω) ∧
      IsGradedTerm (hodgeTatePolyTruncated (E := E) P hP) (polyTruncationStep (E := E) P hP) i (Ω ≫ formShift k i) := by
  constructor
  · exact ⟨(siftedLanIso k (completeD_siftedColimits p k) (ordinaryFormsDiagram k i ≫ (pCompletionReflection p k).1)).postcomp
      (completeDInclusion p k)⟩
  · sorry -- Postnikov cofiber は H^i[−i]。Thm 6.3 の自然な η^i と polyForms_boundedComparison

/-- 完備圏内で延長した gr^i Fil Δ̄ ≃ (∧^i L)^∧[−i]。 -/
theorem hodgeTateFiltration_gr (i : ℕ) :
    IsGradedTerm (filtrationUnderlying (E := E) P hP)
      (fun j => F2.Presentable.postcomposeFunctorHom (completeDInclusion p _) (hodgeTateFiltration_step (E := E) P hP j)) i
      (cotangentWedge P i ≫ formShift (A ⧸ P.ideal) i) := by
  sorry -- hodgeTatePoly_gr の回収同型と cofiber 四角形を完備圏内で延長。導来完備化は完全

/-- 概要：filtration は exhaustive：**完備圏の余極限で** colim_i^{comp} Fil_i Δ̄_R ≃ Δ̄_R（D(k) の余極限で述べるなら LΛ_p を付ける、W9-I-26）。
方針：完備圏内の Kan 延長は ℕ 添字の（完備化した）余極限と交換、Poly 上は有限段で止まる（`hodgeTatePoly_bounded`）。
規約：Δ̄ = Δ ⊗ A/d は p 完備（Δ は (p,d) 完備）。
使われ方：連結性・離散性の議論（A3・A5）。 -/
theorem hodgeTateFiltration_exhaustive (X : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (evaluateFunctorAt X) (hodgeTateTower (E := E) P hP).augmentation) := by
  sorry -- 各多項式で有限段以後の余単位が可逆。完備圏内で二つの余極限を交換

/-- 概要：Fil_0 Δ̄_R ≃ LΛ_p R（animated な導来 p 完備化）、すなわち単位 R → Δ̄_R（E3 の `unit` の材料）。
方針：Poly 上で τ^{≤0} Δ̄_P = H⁰ = P^∧（Thm 6.3 の η⁰）、完備圏で Kan 延長。
規約：離散 R では LΛ_p R は一般に離散でない（W9-I-29）。E3 の `completionRing R` = H⁰(LΛ_p R) との関係は perfd の段で（a5-design §7.1）。
使われ方：A4（単位）、E3 の `unit`・`h0`。 -/
abbrev completedRealization (k : Type u) [CommRing k] :=
  animatedCompletion p k ≫ animatedCompleteInclusion p k ≫ animatedCAlgRealization (E := E) k

def hodgeTateFiltration_zero :
    FunctorIso (hodgeTateFiltration (E := E) P hP 0 ≫ completeDInclusion p _)
      (completedRealization (E := E) (p := p) (A ⧸ P.ideal) ≫ E.forget _) := by
  sorry -- 多項式で η⁰ は H⁰(Δ̄)=P^∧ を同定。両辺を完備圏内で延長

/-- 概要：Fil_0 → Δ̄ を **CAlg_k の自然変換**として（W9-I-30）：Poly 上で H⁰(Δ̄_P) = P^∧ は coconnective な E∞ 代数 Δ̄_P の連結被覆で
H⁰(Δ̄_P) → Δ̄_P は E∞ 代数の射、LΛ_p は CAlg に持ち上がる（G-A2-9）ので CAlg_k で Kan 延長。
方針：A7-1 の `animatedCompletion`、`derivedPrismaticCohomology` の CAlg 値。
規約：`FunctorHom`（CAlg_k 値の関手の圏の射）。E3 の `unit` は H⁰ の環準同型ではなくこれから作る。
使われ方：A4-3 `e3Unit`。 -/
def hodgeTateUnitData :
    { η : FunctorHom (completedRealization (E := E) (p := p) (A ⧸ P.ideal)) (reducedDelta (E := E) P hP) //
      (hodgeTateFiltration_zero (E := E) P hP).hom ≫ F2.Presentable.postcomposeFunctorHom (E.forget _) η =
        F2.Presentable.postcomposeFunctorHom (completeDInclusion p _) (hodgeTateAugmentation (E := E) P hP 0) } := by
  sorry -- Poly 上で coconnective な Δ̄ の連結被覆の E∞ 射を完備圏内で延長。
        -- 忘却後は HTTower の第0脚（G-A2-9）

def hodgeTateUnitCAlg := (hodgeTateUnitData (E := E) P hP).val

/-- 完備化前の R を始点とする単位。A4 は離散入力、A7 は完備入力へ制限して使う。 -/
def hodgeTateUnitFromInput : FunctorHom (animatedCAlgRealization (E := E) (A ⧸ P.ideal)) (reducedDelta (E := E) P hP) :=
  F2.Presentable.postcomposeFunctorHom (animatedCAlgRealization (E := E) _) (animatedCompletionUnit p _) ≫
    hodgeTateUnitCAlg (E := E) P hP

end SerrePositivity.BhattScholze.Prismatic
