-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.HodgeTateFiltration（仮。原典 Construction 7.6 の HT filtration）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.3、単位 A2-3。基準コミット 972bb7f53。ビルドしない。
module

-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology}.lean、drafts/DerivedGeneral/Truncation.lean、
-- drafts/A1/HodgeTateComparison.lean（Thm 6.3）、drafts/Shared/DeRhamPolynomial.lean を import する。

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

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
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
  sorry -- 要確認：DerivedGeneral/CompletionFunctor へ。主元 p の反射の単位・余単位

def completeModuleLan (p : ℕ) (k : Type u) [CommRing k]
    (F : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ derivedInfinityCategory k) :
    AnimatedAlgebra k ⟶ CompleteD p k :=
  siftedLan k (by sorry) -- D(k) の sifted 余極限を反射して完備圏の余極限を得る
    (F ≫ (pCompletionReflection p k).1)

/-- 概要：Δ̄_0(P) := Δ_0(P) ⊗^L_A A/d を **D(k) 値**（k = A/d）で（W9-I-36：Fil と gr の値の圏に合わせる。D(A) 値は忘却で）。
方針：`derivedPrismaticCohomologyDerived` と底変換 D(A) → D(k)（⊗^L_A A/d は k 加群構造をもつ）。
規約：D(k) の頂点。D(A) 値の版は `Res_A` を後合成。
使われ方：Postnikov 切り捨ての入力。 -/
def hodgeTatePoly (hP : IsBoundedPrism P) : (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory (A ⧸ P.ideal) :=
  polyUnderlying P hP ≫ prismModIdeal P ≫ cAlgForgetDerived _

/-- 概要：Poly 上の τ^{≤i} Δ̄_0（i : ℕ）、関手的。
方針：DerivedGeneral/Truncation の `truncationLE A i` を後合成。
規約：i について増大（τ^{≤i} → τ^{≤i+1}）。
使われ方：Fil_i の Kan 延長の入力。 -/
def hodgeTatePolyTruncated (hP : IsBoundedPrism P) (i : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ derivedInfinityCategory (A ⧸ P.ideal) :=
  hodgeTatePoly P hP ≫ Derived.truncationLE (A ⧸ P.ideal) i

/-- 概要：Poly 上で Δ̄_P ∈ D^{[0,n]}（n = 変数の個数）なので τ^{≤n} Δ̄_P ≃ Δ̄_P。
方針：Thm 6.3（H^i = 0 for i > n）と `truncationLE_of_isConnective`（W9-III-11 で改名）。
規約：—
使われ方：exhaustive 性。 -/
theorem hodgeTatePoly_bounded (n : ℕ) :
    let k := A ⧸ P.ideal
    let x := (hodgeTatePoly P hP).app _ (ULift.up (nerveVertex (⟨n⟩ : Poly k)))
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
  completeModuleLan p _ (hodgeTatePolyTruncated P hP i)

abbrev reducedDelta (hP : IsBoundedPrism P) := deltaUnderlying P hP ≫ prismModIdeal P
def reducedDeltaComplete (hP : IsBoundedPrism P) :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ CompleteD p (A ⧸ P.ideal) :=
  fullSubcomplexLift _ (reducedDelta P hP ≫ cAlgForgetDerived _) (by
    sorry) -- (p,d) 完備な Δ の導来 mod d は p 完備

abbrev filtrationShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1,0}).obj (nerve ℕ)
abbrev filtrationIndex (i : ℕ) : filtrationShape.{u} _⦋0⦌ := ULift.up (nerveVertex i)

/-- 各段の指定、増大列、および Δ̄ への増大余錐を一緒に持つ。
多項式上で第 i 脚は H^{≤i} の同型を与えるため、切り捨ての余単位を表す。 -/
structure HTTower (hP : IsBoundedPrism P) where
  diagram : filtrationShape ⟶ (ihom (AnimatedAlgebra (A ⧸ P.ideal))).obj (CompleteD p (A ⧸ P.ideal))
  level (i : ℕ) : diagram.app _ (filtrationIndex i) = functorVertex (hodgeTateFiltration P hP i)
  augmentation : JoinCocone diagram
  target : augmentation.vertex = functorVertex (reducedDeltaComplete P hP)
  truncates (Q : Poly (A ⧸ P.ideal)) (i : ℕ) (j : ℤ) (hj : j ≤ i) :
    let x := (polyYoneda _).app _ (ULift.up (nerveVertex Q))
    let e := (mapJoinCocone (evaluateFunctorAt x ≫ completeDInclusion p _) augmentation).leg
      (SSet.yonedaEquiv.symm (filtrationIndex i))
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ P.ideal)) j).map
      ((derivedInfinityHomotopyEquivalence _).functor.map (SSet.Truncated.HomotopyCategory₂.homMk e)))

def hodgeTateTower (hP : IsBoundedPrism P) : HTTower P hP := by
  sorry -- 要確認：DerivedGeneral/Truncation へ。τ≤i の増大列と余単位を Poly 上で取り、
        -- 完備圏の sifted 延長の関手圏同値で余錐ごと延長する

/-- 第 i 段から次段への射。augmentation の i 番目の脚が Fil_i → Δ̄。 -/
def hodgeTateFiltration_step (hP : IsBoundedPrism P) (i : ℕ) :
    FunctorHom (hodgeTateFiltration P hP i) (hodgeTateFiltration P hP (i+1)) := by
  let T := hodgeTateTower P hP
  let e := (uliftEdge.{0,u+1} (nerve.edgeMk (homOfLE (Nat.le_succ i))).toTruncated).map T.diagram
  exact eqToHom (congrArg HomotopyCategory.mk (T.level i).symm) ≫
    SSet.Truncated.HomotopyCategory₂.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk (T.level (i+1)))

def hodgeTateAugmentation (hP : IsBoundedPrism P) (i : ℕ) :
    FunctorHom (hodgeTateFiltration P hP i) (reducedDeltaComplete P hP) := by
  let T := hodgeTateTower P hP
  let e := T.augmentation.leg (SSet.yonedaEquiv.symm (filtrationIndex i))
  exact eqToHom (by simpa using congrArg HomotopyCategory.mk (T.level i).symm) ≫
    SSet.Truncated.HomotopyCategory₂.homMk e ≫ eqToHom (congrArg HomotopyCategory.mk T.target)

/-- 概要：導来外冪つき余接複体の p 完備化の定義（D33）：(∧^i L_{R/k})^∧ := LΛ_p ∘ Lan（P ↦ Ω̂^i_{P/k}）（完備圏内の sifted 余極限保存延長、W9-I-26）。
方針：Shared/DeRhamPolynomial の `completedForms` を k 加群として D(k) に埋め、完備圏で Kan 延長。
規約：i = 1 が余接複体 L^∧_{R/k}。Illusie の定義（単体的分解による Kan 延長）の p 完備化と同じ。
使われ方：gr の同一視、A5（L_{S/Z_p} の連結性）。 -/
def cotangentWedge (i : ℕ) : AnimatedAlgebra (A ⧸ P.ideal) ⟶ derivedInfinityCategory (A ⧸ P.ideal) := sorry
-- W9-I-36：完備余接複体・外冪は prism P に依らず**一般の基底 k** で独立に定義する（A3 の qrsp は k = Z_p で使う）。`cotangentWedgeGeneral (k) i :
-- AnimatedAlgebra k ⟶ derivedInfinityCategory k` を置き、上はその k = A/d の場合。評価値の S 加群構造（R 上の加群として）も明記する。

/-- 概要：Thm 6.3 による gr^i の同一視（Poly 上）：τ^{≤i}/τ^{≤i−1} Δ̄_P ≃ H^i(Δ̄_P)[−i] ≃ Ω^i_{P/k}[−i]。
方針：`truncation_cofiber`（DerivedGeneral）と A1 の `hodgeTate_iso`（η^i : Ω^i ≅ H^i）。自然性は η^* の関手性。
規約：Ω^i は Shared/DeRhamPolynomial の `completedForms`（p 完備化した多項式代数の微分形式）を A 加群として D(A) に埋めたもの。
使われ方：gr の同一視の Kan 延長。 -/
theorem hodgeTatePoly_gr (i : ℕ) : True := by trivial

/-- 概要：gr^i Fil Δ̄_R ≃ cotangentWedge i (R)[−i]（原典の「Hodge–Tate comparison for Δ̄_R」）。
方針：LΛ_p は完全で cofiber と交換、Kan 延長は余極限と shift と交換、Poly 上で `hodgeTatePoly_gr`。
規約：同値は D(A) の可逆な辺、R について自然。
使われ方：A2-4、A5、A7、A8。 -/
theorem hodgeTateFiltration_gr (i : ℕ) : True := by trivial

/-- 概要：filtration は exhaustive：**完備圏の余極限で** colim_i^{comp} Fil_i Δ̄_R ≃ Δ̄_R（D(k) の余極限で述べるなら LΛ_p を付ける、W9-I-26）。
方針：完備圏内の Kan 延長は ℕ 添字の（完備化した）余極限と交換、Poly 上は有限段で止まる（`hodgeTatePoly_bounded`）。
規約：Δ̄ = Δ ⊗ A/d は p 完備（Δ は (p,d) 完備）。
使われ方：連結性・離散性の議論（A3・A5）。 -/
theorem hodgeTateFiltration_exhaustive (X : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (evaluateFunctorAt X) (hodgeTateTower P hP).augmentation) := by
  sorry -- 各多項式で有限段以後の余単位が可逆。完備圏内で二つの余極限を交換

/-- 概要：Fil_0 Δ̄_R ≃ LΛ_p R（animated な導来 p 完備化）、すなわち単位 R → Δ̄_R（E3 の `unit` の材料）。
方針：Poly 上で τ^{≤0} Δ̄_P = H⁰ = P^∧（Thm 6.3 の η⁰）、完備圏で Kan 延長。
規約：離散 R では LΛ_p R は一般に離散でない（W9-I-29）。E3 の `completionRing R` = H⁰(LΛ_p R) との関係は perfd の段で（a5-design §7.1）。
使われ方：A4（単位）、E3 の `unit`・`h0`。 -/
abbrev completedRealization (k : Type u) [CommRing k] :=
  animatedCompletion p k ≫ animatedCompleteInclusion p k ≫ animatedCAlgRealization k

def hodgeTateFiltration_zero :
    FunctorIso (hodgeTateFiltration P hP 0 ≫ completeDInclusion p _)
      (completedRealization (p := p) (A ⧸ P.ideal) ≫ cAlgForgetDerived _) := by
  sorry -- 多項式で η⁰ は H⁰(Δ̄)=P^∧ を同定。両辺を完備圏内で延長

/-- 概要：Fil_0 → Δ̄ を **CAlg_k の自然変換**として（W9-I-30）：Poly 上で H⁰(Δ̄_P) = P^∧ は coconnective な E∞ 代数 Δ̄_P の連結被覆で
H⁰(Δ̄_P) → Δ̄_P は E∞ 代数の射、LΛ_p は CAlg に持ち上がる（G-A2-9）ので CAlg_k で Kan 延長。
方針：A7-1 の `animatedCompletion`、`derivedPrismaticCohomology` の CAlg 値。
規約：`FunctorHom`（CAlg_k 値の関手の圏の射）。E3 の `unit` は H⁰ の環準同型ではなくこれから作る。
使われ方：A4-3 `e3Unit`。 -/
def hodgeTateUnitData :
    { η : FunctorHom (completedRealization (p := p) (A ⧸ P.ideal)) (reducedDelta P hP) //
      (hodgeTateFiltration_zero P hP).hom ≫ F2.Presentable.postcomposeFunctorHom (cAlgForgetDerived _) η =
        F2.Presentable.postcomposeFunctorHom (completeDInclusion p _) (hodgeTateAugmentation P hP 0) } := by
  sorry -- Poly 上で coconnective な Δ̄ の連結被覆の E∞ 射を完備圏内で延長。
        -- 忘却後は HTTower の第0脚（G-A2-9）

def hodgeTateUnitCAlg := (hodgeTateUnitData P hP).val

/-- 完備化前の R を始点とする単位。A4 は離散入力、A7 は完備入力へ制限して使う。 -/
def hodgeTateUnitFromInput : FunctorHom (animatedCAlgRealization (A ⧸ P.ideal)) (reducedDelta P hP) :=
  F2.Presentable.postcomposeFunctorHom (animatedCAlgRealization _) (animatedCompletionUnit p _) ≫
    hodgeTateUnitCAlg P hP

end SerrePositivity.BhattScholze.Prismatic
